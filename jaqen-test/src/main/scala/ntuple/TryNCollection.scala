package ntuple

object TryNCollection {
  def main(args: Array[String]) {
    case class Person(val name: String, val ssn: String)
    case class SSN(val ssn: String, val gender: String)
    val c = new NCollectionContext
    val people = c.input[Person]("people")
    val ssns = c.input[SSN]("ssns")
    val r = for ((p, s) <- people.keyedBy(_.ssn).join(ssns.keyedBy(_.ssn))) yield (p.name, s.gender)
    r.output("name_gender")
    c.printPlan


    println()
    println("wordcount")
    case class Tweet(val content: String)

    val c1 = new NCollectionContext

    val input = c1.input[Tweet]("tweets")

    input.flatMap(_.content.split(" ")).keyedBy[String]((s) => s).countByKey.output("wordcount")

    c1.printPlan

    val exec = new InMemoryExecutor()
    exec.register("tweets", List(Tweet("a b c"), Tweet("c d e")))
    val out = exec.execute(c1)
    println(out)
    for (i <- exec.readOutput("wordcount")) {
      println(i)
    }
  }
}