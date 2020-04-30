package soot.jimple.spark.pag;

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

import java.util.*;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import soot.AnySubType;
import soot.Context;
import soot.RefLikeType;
import soot.Type;
import soot.jimple.spark.sets.PointsToSetInternal;
import soot.toolkits.scalar.Pair;

/**
 * Represents a simple variable node (Green) in the pointer assignment graph.
 *
 * @author Ondrej Lhotak
 */
public abstract class VarNode extends ValNode implements Comparable {
  public VarNode parent;
  public List<VarNode> members = new LinkedList<VarNode>();
  public int simple_in = 0, load_in = 0;
  public int K;

  public boolean alone() {
    return simple_in == 1 && load_in == 0;
  }

  public void new_p2set() {
    if (p2set != null) {
      PointsToSetInternal newp2set = pag.getSetFactory().newSet(type, pag);
      newp2set.addAll(p2set, null);
      p2set = newp2set;
    }
    else {
      p2set = pag.getSetFactory().newSet(type, pag);
    }
  }
//  public Set<VarNode> S = new HashSet<VarNode>();

  public VarNode find() {
//    return this;
    if (parent == this) return this;
//    parent = parent.find();
//    if (parent.getP2Set().instant_size() != p2set.instant_size()) parent = this;
    return parent.find();
  }

  private static final Logger logger = LoggerFactory.getLogger(VarNode.class);

  public Context context() {
    return null;
  }

  /** Returns all field ref nodes having this node as their base. */
  public Collection<FieldRefNode> getAllFieldRefs() {
    if (fields == null) {
      return Collections.emptyList();
    }
    return fields.values();
  }

  /**
   * Returns the field ref node having this node as its base, and field as its field; null if nonexistent.
   */
  public FieldRefNode dot(SparkField field) {
    return fields == null ? null : fields.get(field);
  }

  public int compareTo(Object o) {
    VarNode other = (VarNode) o;
    if (other.finishingNumber == finishingNumber && other != this) {
      logger.debug("" + "This is: " + this + " with id " + getNumber() + " and number " + finishingNumber);
      logger.debug("" + "Other is: " + other + " with id " + other.getNumber() + " and number " + other.finishingNumber);
      throw new RuntimeException("Comparison error");
    }
//    return other.finishingNumber - finishingNumber;
//    return finishingNumber - other.finishingNumber;
    if (other.K == K) {
        return other.finishingNumber - finishingNumber;
    }
    else {
      return other.K - K;
    }
  }

  public void setFinishingNumber(int i) {
    finishingNumber = i;
    if (i > pag.maxFinishNumber) {
      pag.maxFinishNumber = i;
    }
  }

  public int getFinishingNumber() { return finishingNumber; }

  /** Returns the underlying variable that this node represents. */
  public Object getVariable() {
    return variable;
  }

  /**
   * Designates this node as the potential target of a interprocedural assignment edge which may be added during on-the-fly
   * call graph updating.
   */
  public void setInterProcTarget() {
    interProcTarget = true;
  }

  /**
   * Returns true if this node is the potential target of a interprocedural assignment edge which may be added during
   * on-the-fly call graph updating.
   */
  public boolean isInterProcTarget() {
    return interProcTarget;
  }

  /**
   * Designates this node as the potential source of a interprocedural assignment edge which may be added during on-the-fly
   * call graph updating.
   */
  public void setInterProcSource() {
    interProcSource = true;
  }

  /**
   * Returns true if this node is the potential source of a interprocedural assignment edge which may be added during
   * on-the-fly call graph updating.
   */
  public boolean isInterProcSource() {
    return interProcSource;
  }

  /** Returns true if this VarNode represents the THIS pointer */
  public boolean isThisPtr() {
    if (variable instanceof Pair) {
      Pair o = (Pair) variable;
      return o.isThisParameter();
    }

    return false;
  }

  /* End of public methods. */

  VarNode(PAG pag, Object variable, Type t) {
    super(pag, t);
    parent = this;
    if (!(t instanceof RefLikeType) || t instanceof AnySubType) {
      throw new RuntimeException("Attempt to create VarNode of type " + t);
    }
    this.variable = variable;
    pag.getVarNodeNumberer().add(this);
    setFinishingNumber(++pag.maxFinishNumber);
//    members.add(this);
  }

  /** Registers a frn as having this node as its base. */
  void addField(FieldRefNode frn, SparkField field) {
    if (fields == null) {
      fields = new HashMap<SparkField, FieldRefNode>();
    }
    fields.put(field, frn);
  }

  /* End of package methods. */

  protected Object variable;
  protected Map<SparkField, FieldRefNode> fields;
  protected int finishingNumber = 0;
  protected boolean interProcTarget = false;
  protected boolean interProcSource = false;
  protected int numDerefs = 0;

  public void mergeWith(VarNode other) {
    if (other.replacement != other) {
      throw new RuntimeException("Shouldn't happen in VarNode merge");
    }

    if (replacement != this) {
      throw new RuntimeException("Shouldn't happen in VarNode merge");
    }

    VarNode myRep = (VarNode)getReplacement();
    if (other == myRep) {
      return;
    }

    if (other.p2set != myRep.p2set && other.p2set != null && !other.p2set.isEmpty()) {
      if (myRep.p2set == null || myRep.p2set.isEmpty()) {
        myRep.p2set = other.p2set;
      } else {
        myRep.p2set.mergeWith(other.p2set);
      }
    }
    if (other.p2set != null && other.p2set.getNewSet().isEmpty()) other.p2set = null;

    pag.mergedWith(myRep, other);
    other.replacement = myRep;
    if (other.isInterProcTarget() && !myRep.isInterProcTarget()) {
      for (VarNode u : myRep.members) u.setInterProcTarget();
    }
    else if (!other.isInterProcTarget() && myRep.isInterProcTarget()) {
      for (VarNode u : other.members) u.setInterProcTarget();
    }

//    if (myRep.members.size() > other.members.size())
    myRep.members.addAll(other.members);
//    else {
//      other.members.addAll(myRep.members);
//      myRep.members = other.members;
//    }
//    other.members = null;
  }
}
