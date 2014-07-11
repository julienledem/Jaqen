package ntuple

import scala.collection.immutable.List

sealed trait NCollection[T] {

  val context: NCollectionContext

  def map[U](f: T => U): NCollection[U] = new MappedNCollection(this, f)
  def foreach[U](f: T => U): Unit = context.outputs :+= new ForEachedNCollection(this, f)
  def flatMap[U](f: T => TraversableOnce[U]): NCollection[U] = new FlatMappedNCollection(this, f)
  def withFilter(q: T => Boolean): NCollection[T] = new FilteredNCollection(this, q)

  def keyedBy[K](f: T => K): KeyedNCollection[K, T] = new KeyedNCollection(this, f)

  def output(name: String): NCollection[T] = {
    val output = new NamedOutputNCollection(this, name)
    context.outputs :+= output
    output
  }

}

object NCollectionMacros {

}

class InputNCollection[T](val context: NCollectionContext, val name: String) extends NCollection[T]

abstract class NCollectionWithPredecessors[T](val predecessors: List[NCollection[_]]) extends NCollection[T] {
  val context = predecessors.foldLeft(predecessors.head.context)((acc, next) => if (acc == next.context) acc else throw new IllegalArgumentException("can not mix elements from different contexts"))
}

class MappedNCollection[T, PT](val predecessor: NCollection[PT], val f: PT => T) extends NCollectionWithPredecessors[T](List(predecessor))

class FlatMappedNCollection[T, PT](val predecessor: NCollection[PT], val f: PT => TraversableOnce[T]) extends NCollectionWithPredecessors[T](List(predecessor))

class FilteredNCollection[T](val predecessor: NCollection[T], val q: T => Boolean) extends NCollectionWithPredecessors[T](List(predecessor))

abstract class Aggregator[T, AGG] {

  def add(ts: TraversableOnce[T]): Unit

  def combine(other: Aggregator[T, AGG]): Unit

  def result: Option[AGG]

}

class DefaultAggregator[T, AGG] (initialOp: (T) => AGG, addOp: (AGG, T) => AGG, combineOp: (AGG, AGG) => AGG) {

  private var current: Option[AGG] = None

  def add(ts:TraversableOnce[T]): Unit = if (!ts.isEmpty) current = current match {
    case None => {
      val it = ts.toIterator
      val initial = initialOp(it.next)
      Some(ts.foldLeft(initial)(addOp(_,_)))
    }
    case Some(v) => Some(ts.foldLeft(v)(addOp(_,_)))
  }

  def combine(other: Aggregator[T, AGG]): Unit = current = (current, other.result) match {
    case (None,  _) => other.result
    case (Some(v1), Some(v2)) => Some(combineOp(v1, v2))
    case (_, None) => current
  }

  def result: Option[AGG] = current

}

class KeyedNCollection[K, T](val predecessor: NCollection[T], val f: T => K) extends NCollectionWithPredecessors[T](List(predecessor)) {

  def join[U](other: KeyedNCollection[K, U]): Joined2NCollection[K, T, U] = new Joined2NCollection(this, other)
  def join[U, V](other: Joined2NCollection[K, U, V]): Joined3NCollection[K, T, U, V] = new Joined3NCollection(this, other.predecessor1, other.predecessor2)
  def join[U, V, W](other: Joined3NCollection[K, U, V, W]): NCollection[(T, U, V, W)] = new Joined4NCollection(this, other.predecessor1, other.predecessor2, other.predecessor3)

  /**
   * similar to aggregateByKey but does not require a zero element
   */
  def aggregateByKeyNZ[U](initial: (T) => U, seqop: (U, T) => U, combop: (U, U) => U): KeyedNCollection[K, (K,U)] =
    new KeyedNCollection[K, (K, U)](new AggregatedNCollection(this, initial, seqop, combop), _._1)

    /**
     * based on scala collections aggregate method
     * @param U is the type we aggregate on
     * @param T is the type we aggregate
     * @param z is the zero for U
     * @param combop is an associative law on U
     * @param seqop knows how to add T to the aggregate U.
     */
  def aggregateByKey[U](z: U, seqop: (U, T) => U, combop: (U, U) => U): KeyedNCollection[K, (K,U)] =
    aggregateByKeyNZ[U]((t) => seqop(z, t), seqop, combop)

  def foldByKey(f: (T, T) => T) = aggregateByKeyNZ[T]((t) => t, f, f)

  def countByKey = aggregateByKeyNZ[Long]((t) => 1, (c, t) => c + 1 , _+_)

}

class AggregatedNCollection[K, T, PT](val predecessor: KeyedNCollection[K, PT], val initial: (PT) => T, val seqop: (T, PT) => T, val combop: (T, T) => T) extends NCollectionWithPredecessors[(K, T)](List(predecessor))

abstract class JoinedNCollection[K, V](predecessors: List[KeyedNCollection[K,_]]) extends NCollectionWithPredecessors[V](predecessors)

class Joined2NCollection[K, T, U](
    val predecessor1: KeyedNCollection[K, T],
    val predecessor2: KeyedNCollection[K, U]) extends JoinedNCollection[K, (T, U)](List(predecessor1, predecessor2)) {

  def join[V](other: KeyedNCollection[K, V]): Joined3NCollection[K, T, U, V] = new Joined3NCollection(predecessor1, predecessor2, other)
  def join[V, W](other: Joined2NCollection[K, V, W]): NCollection[(T, U, V, W)] = new Joined4NCollection(predecessor1, predecessor2, other.predecessor1, other.predecessor2)
}

class Joined3NCollection[K, T, U, V](
    val predecessor1: KeyedNCollection[K, T],
    val predecessor2: KeyedNCollection[K, U],
    val predecessor3: KeyedNCollection[K, V]) extends JoinedNCollection[K, (T, U, V)](List(predecessor1, predecessor2, predecessor3)) {

  def join[W](other: KeyedNCollection[K, W]): NCollection[(T, U, V, W)] = new Joined4NCollection[K, T, U, V, W](predecessor1, predecessor2, predecessor3, other)
}

class Joined4NCollection[K, T, U, V, W](
    val predecessor1: KeyedNCollection[K, T],
    val predecessor2: KeyedNCollection[K, U],
    val predecessor3: KeyedNCollection[K, V],
    val predecessor4: KeyedNCollection[K, W]) extends JoinedNCollection[K, (T, U, V, W)](List(predecessor1, predecessor2, predecessor3, predecessor4)) {
}

abstract class OutputNCollection[T](predecessors: List[NCollection[_]]) extends NCollectionWithPredecessors[T](predecessors)

class ForEachedNCollection[PT, U](val predecessor: NCollection[PT], val f: PT => U) extends OutputNCollection[PT](List(predecessor))

class NamedOutputNCollection[T](val predecessor: NCollection[T], val name: String) extends OutputNCollection[T](List(predecessor))


class NCollectionContext {

  private[ntuple] var inputs: List[InputNCollection[_]] = List.empty
  private[ntuple] var outputs: List[OutputNCollection[_]] = List.empty

  def input[T](name: String): NCollection[T] = {
    val input = new InputNCollection[T](this, name)
    inputs :+= input
    input
  }

  def keyedInput[T](name: String): NCollection[T] = {
    val input = new InputNCollection[T](this, name)
    inputs :+= input
    input
  }

  def printPlan = {

    def indentString(size: Int) = (0 to size).foldLeft("") { (acc,n) => acc + " " }

    def printPredecessorPlan(collections: List[NCollection[_]], indent: Int): Unit = {
      for (c <- collections) {
        c match {
          case cp: NCollectionWithPredecessors[_] => printPredecessorPlan(cp.predecessors, indent + 2)
          case _ =>
        }
        println(indentString(indent) + (c match {
          case ic:  InputNCollection[_] => "input: " + ic.name
          case mc:  MappedNCollection[_, _] => "map"
          case fmc: FlatMappedNCollection[_, _] => "flatMap"
          case fc:  FilteredNCollection[_] => "filter"
          case kc:  KeyedNCollection[_, _] => "keyed"
          case jc:  JoinedNCollection[_, _] => "join"
          case ac:  AggregatedNCollection[_, _, _] => "agg"
          case fec: ForEachedNCollection[_, _] => "foreach"
          case noc: NamedOutputNCollection[_] => "output: " + noc.name
          case p: NCollectionWithPredecessors[_] => p.getClass().getName() + "?" // TODO: figure out why I get a warning without this...
        }))
      }
    }

    printPredecessorPlan(outputs, 0)
    println()
  }

  def getPlan: List[OutputNCollection[_]] = outputs

}

class InMemoryExecutor {

  private var inputs = Map.empty[String, TraversableOnce[_]]
  private var outputs = Map.empty[String, TraversableOnce[_]]

  def register[T](name: String, data: TraversableOnce[T]) = inputs += (name -> data)

  def readOutput[T](name: String) = outputs(name)

  def execute(context: NCollectionContext) = {

    def toKeyed[K, V](c: KeyedNCollection[K,V]) =
      plan(c).foldLeft(Map.empty[K, List[V]]) {
        (agg, v) => {
          val k = c.f(v)
          agg + (k -> (agg.getOrElse(k, List.empty[V]) :+ v))
        }
      };

    def cross[T1, T2](l1: List[T1], l2: List[T2]) = for (i1 <- l1; i2 <- l2) yield (i1, i2)

    def joinMaps[K, V1, V2](c1: Map[K,List[V1]], c2: Map[K,List[V2]]) =
      for { (k,v1) <- c1
            if (c2.contains(k))
      } yield (k, cross(v1, c2(k)))

    def mapToList[K, V](map: Map[K, List[V]]): TraversableOnce[V] = map.toList.flatMap { case (k,v) => v }

    def plan[T](c: NCollection[T]): TraversableOnce[T] = c match {
      case ic:  InputNCollection[_] => inputs(ic.name).asInstanceOf[TraversableOnce[T]]
      case mc:  MappedNCollection[_, _] => plan(mc.predecessor).map(mc.f)
      case fmc: FlatMappedNCollection[_, _] => plan(fmc.predecessor).flatMap(fmc.f)
      case fc:  FilteredNCollection[_] => plan(fc.predecessor).filter(fc.q)
      case kc:  KeyedNCollection[_, _] => plan(kc.predecessor)
      case j2c: Joined2NCollection[_, _, _] => mapToList(joinMaps(toKeyed(j2c.predecessor1), toKeyed(j2c.predecessor2)))
      case j3c: Joined3NCollection[_, _, _, _] => {
        val j = mapToList(joinMaps(joinMaps(toKeyed(j3c.predecessor1), toKeyed(j3c.predecessor2)), toKeyed(j3c.predecessor3)))
        j.map{ case ((v1, v2), v3) => (v1, v2, v3) }
      }
      case j4c: Joined4NCollection[_, _, _, _, _] => {
        val j = mapToList(joinMaps(joinMaps(joinMaps(toKeyed(j4c.predecessor1), toKeyed(j4c.predecessor2)), toKeyed(j4c.predecessor3)), toKeyed(j4c.predecessor4)))
        j.map { case (((v1, v2), v3), v4) => (v1, v2, v3, v4) }
      }
      case ac:  AggregatedNCollection[_, _, _] => toKeyed(ac.predecessor).toList.map {
          case (k, vl) => (k, vl.tail.foldLeft(ac.initial(vl.head))(ac.seqop))
      }
      case fec: ForEachedNCollection[_, _] => {
        val p = plan(fec.predecessor)
        p.foreach(fec.f)
        p
      }
      case noc: NamedOutputNCollection[_] => {
        val p = plan(noc.predecessor)
        outputs += (noc.name -> p)
        p
      }
    }
    for (c <- context.getPlan) yield plan(c)
  }

}
