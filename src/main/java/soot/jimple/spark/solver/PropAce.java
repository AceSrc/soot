package soot.jimple.spark.solver;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 2002 - 2006 Ondrej Lhotak
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as
 * published by the Free Software Foundation, either version 2.1 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Lesser Public License for more details.
 *
 * You should have received a copy of the GNU General Lesser Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/lgpl-2.1.html>.
 * #L%
 */

import java.util.*;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.Type;
import soot.jimple.spark.pag.AllocDotField;
import soot.jimple.spark.pag.AllocNode;
import soot.jimple.spark.pag.ClassConstantNode;
import soot.jimple.spark.pag.FieldRefNode;
import soot.jimple.spark.pag.NewInstanceNode;
import soot.jimple.spark.pag.Node;
import soot.jimple.spark.pag.PAG;
import soot.jimple.spark.pag.SparkField;
import soot.jimple.spark.pag.VarNode;
import soot.jimple.spark.sets.P2SetVisitor;
import soot.jimple.spark.sets.PointsToSetInternal;
import soot.util.queue.QueueReader;

import static java.lang.Integer.min;

/**
 * Propagates points-to sets along pointer assignment graph using a worklist.
 *
 * @author Ondrej Lhotak
 */

public class PropAce extends Propagator {
  private static final Logger logger = LoggerFactory.getLogger(PropAce.class);
  protected Set<VarNode> varNodeWorkList = new TreeSet<VarNode>();
  protected Map<VarNode, Integer> counter = new HashMap<VarNode, Integer>();

  long total_access = 0, useful_access = 0, edge_cnt = 0;
  long K = 0, merge_cnt = 0;
  int rounds = 0;

  public PropAce(PAG pag) {
    this.pag = pag;
  }

  /** Actually does the propagation. */
  public void propagate() {
    System.out.println("Hello");
    ofcg = pag.getOnFlyCallGraph();
    new realTopoSorter(pag, false).sort();

    for (AllocNode object : pag.allocSources()) {
      handleAllocNode(object);
    }

    Vector<VarNode> varnodes = new Vector<VarNode>();
    for (VarNode p : pag.getVarNodeNumberer()) {
      varnodes.add(p);
    }

    boolean verbose = pag.getOpts().verbose();
    int phase1 = 0, phase2 = 0;
    do {
      System.out.println("Enter First");
      rounds++;
      phase1 = phase2 = 0;
      if (verbose) {
        logger.debug("Worklist has " + varNodeWorkList.size() + " nodes.");
      }

      Date startpos = new Date();

      while (!varNodeWorkList.isEmpty()) {
        VarNode src = varNodeWorkList.iterator().next();
        varNodeWorkList.remove(src);
//        System.out.println(rounds + "  " + src.getFinishingNumber());
        handleVarNode(src);
      }

      Date endpos = new Date();
      phase1 += endpos.getTime() - startpos.getTime();

      if (verbose) {
        logger.debug("Now handling field references");
      }

      startpos = new Date();

      HashSet<Object[]> edgesToPropagate = new HashSet<Object[]>();
      for (Object object : pag.loadSources()) {
        handleFieldRefNode((FieldRefNode) object, edgesToPropagate);
      }
      Set<PointsToSetInternal> nodesToFlush = Collections.newSetFromMap(new IdentityHashMap<PointsToSetInternal, Boolean>());
      for (Object[] pair : edgesToPropagate) {
        PointsToSetInternal nDotF = (PointsToSetInternal) pair[0];
        PointsToSetInternal newP2Set = nDotF.getNewSet();
        VarNode loadTarget = (VarNode) pair[1];

        total_access += newP2Set.size();
        K += min(newP2Set.size(), loadTarget.makeP2Set().size() + loadTarget.makeP2Set().getNewSet().size());
        int pre_size = loadTarget.makeP2Set().getNewSet().size();
        if (loadTarget.makeP2Set().addAll(newP2Set, null)) {
          useful_access += loadTarget.makeP2Set().getNewSet().size() - pre_size;
          varNodeWorkList.add(loadTarget);
        }
        nodesToFlush.add(nDotF);
      }
      for (PointsToSetInternal nDotF : nodesToFlush) {
        nDotF.flushNew();
      }
      endpos = new Date();
      phase2 += endpos.getTime() - startpos.getTime();

      System.out.println("K: " + K + " total: " + total_access + " useful: " + useful_access + " phase1Time: " + phase1 + " phase2Time: " + phase2);
    } while (!varNodeWorkList.isEmpty());

    long cnt = 0;
    for (VarNode u : varnodes) {
      VarNode v = u;
      while (v != v.getReplacement()) v = (VarNode)v.getReplacement();
      cnt += v.getP2Set().size();
    }
    System.out.println(cnt);
    System.out.println(varnodes.size());
  }

  /* End of public methods. */
  /* End of package methods. */

  /**
   * Propagates new points-to information of node src to all its successors.
   */
  protected boolean handleAllocNode(AllocNode src) {
    boolean ret = false;
    Node[] targets = pag.allocLookup(src);
    for (Node element : targets) {
      total_access++;
      K++;
      if (element.makeP2Set().add(src)) {
        useful_access++;
        varNodeWorkList.add((VarNode) element);
        ret = true;
      }
    }
    return ret;
  }

  protected boolean H(final VarNode src, final VarNode snk) {
//    int src_new_sz = src.getP2Set().getNewSet().size();
//    int src_sz = src.getP2Set().size() + src.getP2Set().getNewSet().size();
//    int snk_sz = snk.getP2Set().size() + snk.getP2Set().getNewSet().size();
//    if (snk_sz < src_new_sz && rounds >= 2 && (double)Math.abs(snk_sz - src_sz) <= 10 * rounds) {
//      if (src.getP2Set().getType() == snk.getP2Set().getType()) return true;
//    }
//    if (src.getP2Set().size() >= 50 && 3 * (snk.getP2Set().size() + snk.getP2Set().getNewSet().size()) < src.getP2Set().getNewSet().size()) {
//      if (src.getP2Set().getType() == snk.getP2Set().getType()) return true;
//    }
    return false;
  }

  /**
   * Propagates new points-to information of node src to all its successors.
   */
  protected boolean handleVarNode(final VarNode src) {
    boolean ret = false;
    boolean flush = true;

    if (src.getReplacement() != src) {
      return false;
      //      throw new RuntimeException("Got bad node " + src + " with rep " + src.getReplacement());
    }

    final PointsToSetInternal newP2Set = src.getP2Set().getNewSet();
    if (newP2Set.isEmpty()) {
      return false;
    }

    if (ofcg != null) {
      QueueReader<Node> addedEdges = pag.edgeReader();
      ofcg.updatedNode(src);
      ofcg.build();
      while (addedEdges.hasNext()) {
        edge_cnt++;
        Node addedSrc = (Node) addedEdges.next();
        Node addedTgt = (Node) addedEdges.next();
        ret = true;
        if (addedSrc instanceof VarNode) {
          VarNode edgeSrc = (VarNode) addedSrc.getReplacement();
          if (addedTgt instanceof VarNode) {
            VarNode edgeTgt = (VarNode) addedTgt.getReplacement();


//            total_access += edgeSrc.getP2Set().size();
//            K += min(edgeSrc.getP2Set().size(), edgeTgt.makeP2Set().size() + edgeTgt.makeP2Set().getNewSet().size());
            int pre_size = edgeTgt.makeP2Set().getNewSet().size();
            if (edgeTgt.makeP2Set().addAll(edgeSrc.getP2Set(), null)) {
              varNodeWorkList.add(edgeTgt);
              useful_access += edgeTgt.makeP2Set().getNewSet().size() - pre_size;
              if (edgeTgt == src) {
                flush = false;
              }
            }
          } else if (addedTgt instanceof NewInstanceNode) {
            NewInstanceNode edgeTgt = (NewInstanceNode) addedTgt.getReplacement();
//            total_access += edgeSrc.getP2Set().size();
//            K += min(edgeSrc.getP2Set().size(), edgeTgt.makeP2Set().size() + edgeTgt.makeP2Set().getNewSet().size());
//            int pre_size = edgeTgt.makeP2Set().getNewSet().size();
            if (edgeTgt.makeP2Set().addAll(edgeSrc.getP2Set(), null)) {
              for (Node element : pag.assignInstanceLookup(edgeTgt)) {
                varNodeWorkList.add((VarNode) element);
//                useful_access += edgeTgt.makeP2Set().getNewSet().size() - pre_size;
                if (element == src) {
                  flush = false;
                }
              }
            }
          }
        } else if (addedSrc instanceof AllocNode) {
          VarNode edgeTgt = (VarNode) addedTgt.getReplacement();
//          total_access++;
//          K++;
          if (edgeTgt.makeP2Set().add(addedSrc)) {
//            useful_access++;
            varNodeWorkList.add(edgeTgt);
            if (edgeTgt == src) {
              flush = false;
            }
          }
        } else if (addedSrc instanceof NewInstanceNode && addedTgt instanceof VarNode) {
          final NewInstanceNode edgeSrc = (NewInstanceNode) addedSrc.getReplacement();
          final VarNode edgeTgt = (VarNode) addedTgt.getReplacement();
          addedSrc.getP2Set().forall(new P2SetVisitor() {

            @Override
            public void visit(Node n) {
              if (n instanceof ClassConstantNode) {
                ClassConstantNode ccn = (ClassConstantNode) n;
                Type ccnType = ccn.getClassConstant().toSootType();

                // If the referenced class has not been loaded,
                // we do this now
                SootClass targetClass = ((RefType) ccnType).getSootClass();
                if (targetClass.resolvingLevel() == SootClass.DANGLING) {
                  Scene.v().forceResolve(targetClass.getName(), SootClass.SIGNATURES);
                }

                // We can only create alloc nodes for types that
                // we know
                total_access++;
                K++;
                if (edgeTgt.makeP2Set().add(pag.makeAllocNode(edgeSrc.getValue(), ccnType, ccn.getMethod())))
                  useful_access++;
                varNodeWorkList.add(edgeTgt);
              }
            }

          });
          if (edgeTgt.makeP2Set().add(addedSrc)) {
            if (edgeTgt == src) {
              flush = false;
            }
          }
        }
      }
    }

    Node[] simpleTargets = pag.simpleLookup(src);
    for (Node element : simpleTargets) {
      if (H(src, (VarNode)element)) {
//        System.out.println("merge " + src.getFinishingNumber() + "   " + ((VarNode) element).getFinishingNumber());
        src.getP2Set().addAll(element.getP2Set(), null);
        src.getP2Set().addAll(element.getP2Set().getNewSet(), null);
        src.mergeWith(element);
        element.discardP2Set();
        varNodeWorkList.add((VarNode) src);
        flush = false;
        ret = true;
      }
      if (element.makeP2Set().addAll(newP2Set, null)) {
        varNodeWorkList.add((VarNode) element);
        if (element == src) {
          flush = false;
        }
        ret = true;
      }
    }

    Node[] storeTargets = pag.storeLookup(src);
    for (Node element : storeTargets) {
      final FieldRefNode fr = (FieldRefNode) element;
      final SparkField f = fr.getField();
      ret = fr.getBase().getP2Set().forall(new P2SetVisitor() {
        public final void visit(Node n) {
          AllocDotField nDotF = pag.makeAllocDotField((AllocNode) n, f);
          if (nDotF.makeP2Set().addAll(newP2Set, null)) {
            returnValue = true;
          }
        }
      }) | ret;
    }

    final HashSet<Node[]> storesToPropagate = new HashSet<Node[]>();
    for (final FieldRefNode fr : src.getAllFieldRefs()) {
      final SparkField field = fr.getField();
      final Node[] storeSources = pag.storeInvLookup(fr);
      if (storeSources.length > 0) {
        newP2Set.forall(new P2SetVisitor() {
          public final void visit(Node n) {
            AllocDotField nDotF = pag.makeAllocDotField((AllocNode) n, field);
            for (Node element : storeSources) {
              Node[] pair = { element, nDotF.getReplacement() };
              storesToPropagate.add(pair);
            }
          }
        });
      }
    }
    if (flush) {
      src.getP2Set().flushNew();
    }
    for (Node[] p : storesToPropagate) {
      VarNode storeSource = (VarNode) p[0];
      AllocDotField nDotF = (AllocDotField) p[1];

      total_access += storeSource.getP2Set().size();

      int pre_size = nDotF.makeP2Set().getNewSet().size();
      K += min(storeSource.getP2Set().size(), nDotF.makeP2Set().size() + pre_size);
      if (nDotF.makeP2Set().addAll(storeSource.getP2Set(), null)) {
        ret = true;
        useful_access += nDotF.makeP2Set().getNewSet().size() - pre_size;
      }
    }
    return ret;
  }

  /**
   * Propagates new points-to information of node src to all its successors.
   */
  protected final void handleFieldRefNode(FieldRefNode src, final HashSet<Object[]> edgesToPropagate) {
    final Node[] loadTargets = pag.loadLookup(src);
    if (loadTargets.length == 0) {
      return;
    }
    final SparkField field = src.getField();

    src.getBase().getP2Set().forall(new P2SetVisitor() {

      public final void visit(Node n) {
        AllocDotField nDotF = pag.makeAllocDotField((AllocNode) n, field);
        if (nDotF != null) {
          PointsToSetInternal p2Set = nDotF.getP2Set();
          if (!p2Set.getNewSet().isEmpty()) {
            for (Node element : loadTargets) {
              Object[] pair = { p2Set, element };
              edgesToPropagate.add(pair);
            }
          }
        }
      }
    });
  }

  protected PAG pag;
  protected OnFlyCallGraph ofcg;
}
