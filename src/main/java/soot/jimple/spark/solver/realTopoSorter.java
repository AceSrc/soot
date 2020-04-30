package soot.jimple.spark.solver;

/*-
 * #%L
 * Soot - a J*va Optimization Framework
 * %%
 * Copyright (C) 2002 Ondrej Lhotak
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

import soot.jimple.spark.pag.FieldRefNode;
import soot.jimple.spark.pag.Node;
import soot.jimple.spark.pag.PAG;
import soot.jimple.spark.pag.VarNode;

import java.util.*;

/**
 * Performs a pseudo-topological sort on the VarNodes in a PAG.
 * 
 * @author Ondrej Lhotak
 */

public class realTopoSorter {
  public realTopoSorter(PAG pag, boolean ignoreTypes) {
    this.pag = pag;
    this.ignoreTypes = ignoreTypes;
  }

  /* End of public methods. */
  /* End of package methods. */

  protected boolean ignoreTypes = true;
  protected PAG pag;
  protected int nextFinishNumber = 0;
  protected Map<VarNode, Integer> degs = new HashMap<VarNode, Integer>();
  protected final Queue<VarNode> varNodeWorkList = new LinkedList<VarNode>();
  protected HashSet<VarNode> visited = new HashSet<VarNode>();

  /** Actually perform the topological sort on the PAG. */
  public VarNode[] sort() {
    for (VarNode u : pag.getVarNodeNumberer()) {
      degs.put(u, 0);
    }

    for (VarNode u : pag.getVarNodeNumberer()) {
      for (Node v : pag.simpleLookup(u)) degs.put((VarNode)v, degs.get((VarNode)v) + 1);
    }

    for (VarNode u : pag.getVarNodeNumberer()) {
      if (degs.get(u) == 0) varNodeWorkList.offer(u);
    }

    VarNode[] rt = new VarNode[degs.keySet().size()];
    while (!varNodeWorkList.isEmpty()) {
      VarNode u = varNodeWorkList.poll();
      u.setFinishingNumber(nextFinishNumber++);
      if (visited.contains(u)) {
        System.out.println("Err!");
        System.out.println(degs.get(u));
        return new VarNode[0];
      }
      visited.add(u);

      for (Node v : pag.simpleLookup(u)) {
        degs.put((VarNode)v, degs.get((VarNode)v) - 1);
        if (degs.get((VarNode)v) == 0) varNodeWorkList.offer((VarNode)v);
          if (degs.get((VarNode)v) < 0) {
            System.out.println("!ZERO!");
          }
      }
    }
    for (VarNode v : pag.getVarNodeNumberer()) {
      if (!visited.contains(v)) v.setFinishingNumber(nextFinishNumber++);
    }
    return rt;
  }

  protected void dfsVisit(VarNode n) {
    if (visited.contains(n)) {
      return;
    }
    visited.add(n);
    Node[] succs = pag.simpleLookup(n);
    for (Node element : succs) {
      if (ignoreTypes || pag.getTypeManager().castNeverFails(n.getType(), element.getType())) {
        dfsVisit((VarNode) element);
      }
    }
    n.setFinishingNumber(nextFinishNumber++);
  }
}
