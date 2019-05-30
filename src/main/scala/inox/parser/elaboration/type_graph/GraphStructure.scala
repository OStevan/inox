package inox.parser.elaboration.type_graph

import inox.parser.elaboration.{Constraints, SimpleTypes}

import scala.collection.mutable
import scala.util.parsing.input.{Position, Positional}

trait GraphStructure { self: SimpleTypes with Constraints =>

  import Constraints._
  import Edges._
  import Nodes._
  import SimpleTypes._
  import TypeClasses._

  type Color = Boolean
  val Black: Color = true
  val White: Color = false

  trait Node extends Positional {
    private var counter: Int = 0

    val color: Boolean

    /**
      * Tests if two nodes have the same type information
      * @param other node to compare with
      * @return flag if the information inside is the same
      */
    def nodeInformationEquality(other: Node): Boolean = (this, other) match {
      case (first: TypeNode, second: TypeNode) => first.tpe == second.tpe
      case (_: TypeNode, _: TypeClassNode) => false
      case (first: TypeClassNode, second: TypeClassNode) => first.typeClass == second.typeClass
      case _ => false
    }

    def withPosition(pos: Position): Node = this match {
      case TypeNode(tpe, `color`) => TypeNode(tpe, color).setPos(pos)
      case TypeClassNode(tpeClass) => TypeClassNode(tpeClass).setPos(pos)
    }

    def incSatisfiableCount(): Unit = counter = counter + 1

    def satisfiableCount(): Int = counter

    def hasVars: Boolean

    def isTrivialEnd: Boolean

    override def equals(obj: Any): Boolean
  }

  object Nodes {

    case class TypeNode(tpe: SimpleTypes.Type, color: Color = Black) extends Node {

      setPos(tpe.pos)

      override def equals(obj: Any): Boolean = obj match {
        case TypeNode(other: Unknown, _) => other == tpe
        case other: TypeNode => tpe == other.tpe && pos == other.pos
        case _ => false
      }

      override def isTrivialEnd: Boolean = tpe match {
        case _: SimpleTypes.Unknown => true
        case _ => false

      }

      override def hasVars: Boolean = {
        def hasVarsHelper(tpe: SimpleTypes.Type): Boolean = tpe match {
          case _: Unknown => true
          case _: TypeParameter => true
          case ADTType(_, args) => args.exists(tpe => hasVarsHelper(tpe))
          case FunctionType(froms, to) => froms.exists(tpe => hasVarsHelper(tpe)) && hasVarsHelper(to)
          case TupleType(elems) => elems.exists(tpe => hasVarsHelper(tpe))
          case MapType(from, to) => hasVarsHelper(from) || hasVarsHelper(to)
          case BagType(elem) => hasVarsHelper(elem)
          case SetType(elem) => hasVarsHelper(elem)
          case _ => false
        }

        hasVarsHelper(tpe)
      }
    }

    case class TypeClassNode private(typeClass: TypeClass) extends Node {

      val color: Boolean = White

      override def isTrivialEnd: Boolean = false

      override def hasVars: Boolean = false

      override def equals(obj: Any): Boolean = obj match {
        case other: TypeClassNode => (typeClass == other.typeClass) && (pos == other.pos)
        case _ => false
      }
    }
  }

  trait Edge {
    private var counter = 0

    def incSatisfiableCount(): Unit = counter = counter + 1

    def satisfiableCount(): Int = counter

    def from(): Node

    def to(): Node
  }

  object Edges {

    object ConstructorEdgeDirection {

      trait Direction

      case object Original extends Direction

      case object Decompositional extends Direction

    }

    import ConstructorEdgeDirection._

    case class LessEqualEdge(from: Node, to: Node) extends Edge

    case class ConstructorEdge(from: Node, to: Node, direction: Direction, position: Int) extends Edge

  }

  trait Graph {
    def nodes: Set[Node]

    def edges: Set[Edge]

    def union(other: Graph): Graph

    def nodeEdgesMap: Map[Node, Set[Edge]]
  }

  case class ConstraintGraph private(nodeEdgesMap: Map[Node, Set[Edge]], edges: Set[Edge]) extends Graph {

    override def nodes: Set[Node] = nodeEdgesMap.keySet

    def this(nodes: Set[Node], edges: Set[Edge]) {
      this(ConstraintGraph.makeNodeEdgesMap(nodes, edges), edges)
    }

    override def union(other: Graph): Graph = other match {
      case other: ConstraintGraph =>
        ConstraintGraph(this.nodeEdgesMap.keySet union other.nodeEdgesMap.keySet, this.edges union other.edges)
    }

    def union(other: ConstraintGraph): ConstraintGraph =
      ConstraintGraph(this.nodeEdgesMap.keySet union other.nodeEdgesMap.keySet, this.edges union other.edges)

    def addEdge(edge: Edge): ConstraintGraph = {
      edge match {
        case LessEqualEdge(from, to) =>
          assert(nodeEdgesMap.keySet.contains(from) && nodeEdgesMap.keySet.contains(to))
          new ConstraintGraph(nodeEdgesMap.updated(from, nodeEdgesMap.getOrElse(from, Set()) + edge), edges + edge)
        case ConstructorEdge(from, to, _, _) =>
          assert(nodeEdgesMap.keySet.contains(from) && nodeEdgesMap.keySet.contains(to))
          new ConstraintGraph(nodeEdgesMap.updated(from, nodeEdgesMap.getOrElse(from, Set()) + edge), edges + edge)
      }
    }
  }

  object ConstraintGraph {
    def apply(nodes: Set[Node], edges: Set[Edge]): ConstraintGraph = new ConstraintGraph(nodes, edges)

    def apply(node: Node): ConstraintGraph = new ConstraintGraph(Set(node), Set.empty[Edge])

    def apply(edge: Edge): ConstraintGraph = new ConstraintGraph(Set.empty[Node], Set(edge))

    def empty(): ConstraintGraph = ConstraintGraph(Set.empty[Node], Set.empty[Edge])

    private def makeNodeEdgesMap(nodes: Set[Node], edges: Set[Edge]): Map[Node, Set[Edge]] = {
      var nodeEdgesMap: Map[Node, Set[Edge]] = Map.empty

      nodes.foreach(node => nodeEdgesMap = nodeEdgesMap.updated(node, Set.empty))

      edges.foreach {
        case edge: LessEqualEdge => nodeEdgesMap = nodeEdgesMap.updated(edge.from, nodeEdgesMap.getOrElse(edge.from, Set()) + edge)
        case edge: ConstructorEdge => nodeEdgesMap = nodeEdgesMap.updated(edge.from, nodeEdgesMap.getOrElse(edge.from, Set()) + edge)
      }

      nodeEdgesMap
    }
  }


  def constructSeq(constraints: Seq[Constraint]): ConstraintGraph =
    constraints.map((constraint: Constraint) => construct(constraint)).foldLeft(ConstraintGraph.empty()) {
      case (acc, graph) => acc union graph
    }

  def construct(constraint: Constraint): ConstraintGraph = constraint match {
    case Equals(left, right) =>
      val (leftNode: Node, leftGraph: ConstraintGraph) = construct(left)
      val (rightNode: Node, rightGraph: ConstraintGraph) = construct(right)
      leftGraph union rightGraph union new ConstraintGraph(Set[Node](),
        Set(
          LessEqualEdge(leftNode, rightNode),
          LessEqualEdge(rightNode, leftNode)
        ))
    case HasClass(elem, typeClass) =>
      val (elemNode, elemGraph) = construct(elem)
      val typeClassNode = TypeClassNode(typeClass).withPosition(constraint.pos)
      elemGraph union ConstraintGraph(typeClassNode) union ConstraintGraph(LessEqualEdge(elemNode, typeClassNode))
    case _ =>
      // ignore exists currently
      ConstraintGraph.empty()
  }

  def construct(tpe: SimpleTypes.Type): (Node, ConstraintGraph) = tpe match {
    case SimpleTypes.FunctionType(froms, to) =>
      val (toNode, toGraph) = construct(to)
      val funNode = TypeNode(tpe).withPosition(tpe.pos)

      val startGraph = (ConstraintGraph(funNode)
        union toGraph
        union ConstraintGraph(ConstructorEdge(toNode, funNode, ConstructorEdgeDirection.Original, froms.length))
        union ConstraintGraph(ConstructorEdge(funNode, toNode, ConstructorEdgeDirection.Decompositional, froms.length))
        )

      (funNode,
        froms.foldLeft((0, startGraph))((pair, elem) => {
          val (elemNode, elemGraph) = construct(elem)
          (pair._1 + 1, pair._2
            union elemGraph
            union ConstraintGraph(ConstructorEdge(elemNode, funNode, ConstructorEdgeDirection.Original, pair._1))
            union ConstraintGraph(ConstructorEdge(funNode, elemNode, ConstructorEdgeDirection.Decompositional, pair._1)))

        })._2
      )
    case SimpleTypes.TupleType(elems) =>
      val tupleType = TypeNode(tpe).withPosition(tpe.pos)
      (tupleType,
        elems.foldLeft((0, ConstraintGraph(tupleType)))((pair, elem) => {
          val (elemNode, elemGraph) = construct(elem)
          (pair._1 + 1, pair._2
            union elemGraph
            union ConstraintGraph(ConstructorEdge(elemNode, tupleType, ConstructorEdgeDirection.Original, pair._1))
            union ConstraintGraph(ConstructorEdge(tupleType, elemNode, ConstructorEdgeDirection.Decompositional, pair._1)))

        })._2
      )
    case SimpleTypes.BagType(elemType) =>
      val bagNode = TypeNode(tpe).withPosition(tpe.pos)
      val (elemNode, elemGraph) = construct(elemType)
      (bagNode,
        ConstraintGraph(bagNode)
          union elemGraph
          union ConstraintGraph(ConstructorEdge(elemNode, bagNode, ConstructorEdgeDirection.Original, 0))
          union ConstraintGraph(ConstructorEdge(bagNode, elemNode, ConstructorEdgeDirection.Decompositional, 0))
      )
    case SimpleTypes.SetType(elemType) =>
      val setNode = TypeNode(tpe).withPosition(tpe.pos)
      val (elemNode, elemGraph) = construct(elemType)
      (setNode,
        ConstraintGraph(setNode)
          union elemGraph
          union ConstraintGraph(ConstructorEdge(elemNode, setNode, ConstructorEdgeDirection.Original, 0))
          union ConstraintGraph(ConstructorEdge(setNode, elemNode, ConstructorEdgeDirection.Decompositional, 0))
      )
    case SimpleTypes.ADTType(_, args) =>
      val adtNode = TypeNode(tpe).withPosition(tpe.pos)
      (adtNode,
        args.foldLeft((0, ConstraintGraph(adtNode)))((pair, elem) => {
          val (elemNode, elemGraph) = construct(elem)
          (pair._1 + 1, pair._2
            union elemGraph
            union ConstraintGraph(ConstructorEdge(elemNode, adtNode, ConstructorEdgeDirection.Original, pair._1))
            union ConstraintGraph(ConstructorEdge(adtNode, elemNode, ConstructorEdgeDirection.Decompositional, pair._1)))

        })._2
      )
    case SimpleTypes.MapType(from, to) =>
      val (fromNode, fromGraph) = construct(from)
      val (toNode, toGraph) = construct(to)
      val mapNode = TypeNode(tpe).withPosition(tpe.pos)
      (mapNode,
        ConstraintGraph(mapNode)
          union fromGraph
          union toGraph
          union ConstraintGraph(ConstructorEdge(fromNode, mapNode, ConstructorEdgeDirection.Original, 0))
          union ConstraintGraph(ConstructorEdge(mapNode, fromNode, ConstructorEdgeDirection.Decompositional, 0))
          union ConstraintGraph(ConstructorEdge(toNode, mapNode, ConstructorEdgeDirection.Original, 1))
          union ConstraintGraph(ConstructorEdge(mapNode, toNode, ConstructorEdgeDirection.Decompositional, 1))
      )
    case a: SimpleTypes.Type => (TypeNode(a).withPosition(tpe.pos),
      new ConstraintGraph(Set[Node](TypeNode(a).withPosition(tpe.pos)), Set.empty))
  }

  def saturate(graph: Graph): Graph = graph match {
    case g: ConstraintGraph => saturate(g)
  }

  def saturate(graph: ConstraintGraph): ConstraintGraph = {
    var resultGraph = graph
    val workList: mutable.Queue[Either[Edge, (ConstructorEdge, LessEqualEdge)]] = mutable.Queue() ++ graph.edges.map(a => Left(a))
    while (workList.nonEmpty) {
      val current = workList.dequeue()
      current match {
        case Left(edge: LessEqualEdge) =>
          graph.nodeEdgesMap.getOrElse(edge.to, Set()).foreach {
            case chain: LessEqualEdge =>
              val transitive = LessEqualEdge(edge.from, chain.to)
              workList.enqueue(Left(transitive))
              resultGraph = resultGraph.addEdge(transitive)
            case _ =>
              ()
          }
        case Left(edge@ConstructorEdge(_, to, ConstructorEdgeDirection.Original, _)) =>
          graph.nodeEdgesMap.getOrElse(to, Set()).foreach {
            case chain: LessEqualEdge =>
              workList.enqueue(Right((edge, chain)))
            case _ =>
              ()
          }
        case Right((constructor, lessEqual)) =>
          graph.nodeEdgesMap.getOrElse(lessEqual.to, Set()).foreach {
            case ConstructorEdge(_, to, ConstructorEdgeDirection.Decompositional, position) if position == constructor.position =>
              val created = LessEqualEdge(constructor.from, to)
              workList.enqueue(Left(created))
              resultGraph = resultGraph.addEdge(created)
            case _ =>
              ()
          }
      }
    }
    resultGraph
  }




}
