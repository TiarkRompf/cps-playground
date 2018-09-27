package test1

object Test {

  abstract class Term
  abstract class Type

  case class Const(x: Any) extends Term
  case class Var(x: String) extends Term
  case class Lam(x: String, n: Int, t: Type, y: Term) extends Term
  case class App(f: Term, x: Term) extends Term
  case class Let(x: String, n: Int, y: Term, z: Term) extends Term
  case class Reset(x: Term) extends Term
  case class Shift(x: Term) extends Term
  case class If(c: Term, a: Term, b: Term) extends Term
  case class Exit(x: Term) extends Term
  case class Plus(x: Term, y: Term) extends Term
  case class Times(x: Term, y: Term) extends Term


  case object Unit extends Type
  case object Nat extends Type
  case object Bool extends Type
  case class Fun(x: Type, n: Int, y: EType) extends Type

  // case object Void extends EType
  // case object Simple(x: Type) extends EType
  // case class CPS(x: Type, a: Type) extends EType

  type EType = List[Type]

  val Void = Nil

  def seq(a: EType, b: EType): EType = (a,b) match {
    case (a1::Nil, bs) => bs
    case (a1::as, b1::Nil) => (b1::as)
    case (a1::as, b1::bs) if as == bs => (b1::bs) // generalize?
  }

  def typeInfer(t: Term)(implicit env: Map[String,EType]): List[Type] = t match {
    case Const(x: Int) =>       List(Nat)
    case Const(x: Boolean) =>   List(Bool)
    case Var(x) =>              env(x)
    case Exit(x) =>
      typeCheck(x, List(Nat))
      Void
    case If(c,a,b) =>
      val e1 = typeCheckPrefix(c, List(Bool)) // may effect
      val ty = typeInfer(a)
      typeCheck(b, ty)
      seq(e1,ty)
    case Let(x, n, y, z) => 
      val ty = typeInfer(y)
      val ty1 = typeInfer(z)(env + (x -> List(ty.head)))
      seq(ty,ty1)
    case Lam(x, n, t, y) => 
      val ty = typeInfer(y)(env + (x -> List(t)))
      List(Fun(t, n, ty))
    case App(f, x) => 
      val tf @ (Fun(thx,n,ty)::_) = typeInfer(f)
      val tx = typeCheckPrefix(x, List(thx))
      seq(seq(tf,tx),ty)

    case Reset(x) => //reset(T @cps[T]): T
      val thd::ttl = typeInfer(x)
      assert(thd == ttl.head)
      ttl

    case Shift(x) => //shift((k: T => U) => U): T @cps[U]
      val tf @ (Fun(Fun(tx,n1,tu1),n2,tu2)::Nil) = typeInfer(x)
      assert(tu1 == tu2)
      tx::tu1
  }

  def typeCheckPrefix(t: Term, ty: EType)(implicit env: Map[String,EType]): EType = (t,ty) match {
    case (_,_) =>
      val ty1 = typeInfer(t)
      assert(ty1 startsWith ty)
      ty1
  }

  def typeCheck(t: Term, ty: EType)(implicit env: Map[String,EType]) = (t,ty) match {
    case (_,_) =>
      assert(typeInfer(t) == ty)
  }

/*

  types:

    Void        no continuation
    A           k: A => Void
    A @cps[B]   k: A => B   -->   A => (B => Void) => Void

*/



  import scala.reflect.runtime.universe.{Type => SType, _}
  def fromScala(t: Tree): Term = t match {
    case Literal(Constant(x)) => Const(x)
    case Ident(x) => Var(x.toString)
    case q"exit($x)" => Exit(fromScala(x))
    case q"reset($x)" => Reset(fromScala(x))
    case q"shift($x)" => Shift(fromScala(x))
    case q"($x:${t}) => $y" => 
      Lam(x.toString,1,fromScala1(t),fromScala(y))
    case q"$x + $y" => Plus(fromScala(x),fromScala(y))
    case q"$x * $y" => Times(fromScala(x),fromScala(y))
    case Apply(f,x::Nil) => App(fromScala(f),fromScala(x))
  }

  def fromScala1(t: Tree): Type = t match {
    case tq"Int" => Nat
    case tq"$a => $b" => Fun(fromScala1(a), 1, fromScala1(b)::Nil)
    case _ if t.toString == "<type ?>" => Unit
  }


  def pretty(t: Term): String = t match {
    case Const(x) => x.toString
    case Var(x) => x.toString
    case App(f,x) => s"${pretty(f)}(${pretty(x)})"
    case Lam(x,n,t,y) => s"{ $x: $t => ${pretty(y)}}"
    case Exit(x) => s"exit(${pretty(x)})"
    case Reset(x) => s"reset(${pretty(x)})"
    case Shift(x) => s"shift(${pretty(x)})"
    case Plus(x,y) => s"(${pretty(x)} + ${pretty(y)}"
    case Times(x,y) => s"(${pretty(x)} * ${pretty(y)}"
  }


  def evalStd(t: Term)(k: Any => Any)(implicit env: Map[String,Any]): Any = t match {
    case Const(x: Int) =>       k(x)
    case Const(x: Boolean) =>   k(x)
    case Plus(x,y) =>           evalStd(x) { u => evalStd(y) { v => k(u.asInstanceOf[Int] + v.asInstanceOf[Int]) }}
    case Times(x,y) =>          evalStd(x) { u => evalStd(y) { v => k(u.asInstanceOf[Int] * v.asInstanceOf[Int]) }}
    case Var(x) =>              k(env(x))

    case Lam(x,n,t,y) =>        k((x1:Any) => (k1:Any => Any) => evalStd(y)(k1)(env + (x -> x1))) // same level!

    case App(x,y) =>            evalStd(x) { u => evalStd(y) { v => u.asInstanceOf[Any => (Any => Any) => Any](v)(k) }}

    case If(c,a,b) =>
      evalStd(c) { x => if (x.asInstanceOf[Boolean]) evalStd(a)(k) else evalStd(b)(k) }
  
    case Shift(x) => //shift((k: T => U) => U): T @cps[U]
      evalStd(x) { f => 
        val f1 = f.asInstanceOf[(Any => Any) => (Any => Any) => Any]
        f1((x:Any) => (k1:Any => Any) => k1(k(x)))(x => x) // same level!
      }

    case Reset(x) => 
      k(evalStd(x)(x => x)) // same level

  }



  case class AbortException(x: Any) extends Exception

  def eval0(t: Term)(implicit env: Map[String,Any]): Nothing = t match {
    case Exit(x) =>
      evalN[Nothing](x)(C0,env) { x => throw AbortException(x) }
    // case If(c,a,b) =>
    //   if (eval1(c).asInstanceOf[Boolean]) eval0(a) else eval0(b)
    // case Let(x, n, y, z) => 
    //   val v = eval1(y)
    //   eval0(z)(env + (x -> v))
    case App(f, x) => 
      evalN[Nothing](f)(C0,env) { fv =>
      evalN[Nothing](x)(C0,env) { fx =>
      fv.asInstanceOf[Any=>Nothing](fx) }}
  }


  type Wrap[A] = (Any => A) => A

  abstract class CPS[A] {
  }

  case object C0 extends CPS[Nothing] {
  }

  case class CN[A](next: CPS[A]) extends CPS[Wrap[A]] {
  }


  def evalN[A](t: Term)(cps: CPS[A], env: Map[String,Any])(k: Any => A): A = t match {
    case Const(x: Int) =>       k(x)
    case Const(x: Boolean) =>   k(x)
    case Plus(x,y) =>           evalN(x)(cps,env) { u => evalN(y)(cps,env) { v => k(u.asInstanceOf[Int] + v.asInstanceOf[Int]) }}
    case Times(x,y) =>          evalN(x)(cps,env) { u => evalN(y)(cps,env) { v => k(u.asInstanceOf[Int] * v.asInstanceOf[Int]) }}
    case Var(x) =>              k(env(x))

    case Lam(x,n,t,y) =>        
      val f: Any => Wrap[A] = x1 => k => evalN(y)(cps,env + (x -> x1))(k) // eta-expansion not really required...
      k(f)

    case App(x,y) =>            evalN(x)(cps,env) { u => evalN(y)(cps,env) { v => u.asInstanceOf[Any => Wrap[A]](v)(k) }}

    case If(c,a,b) =>
      evalN(c)(cps,env) { x => if (x.asInstanceOf[Boolean]) evalN(a)(cps,env)(k) else evalN(b)(cps,env)(k) }
  
    case Shift(Lam(x,n,t,y)) => //shift((k: T => U) => U): T @cps[U]

      val f: Wrap[A] = cps match {
        case C0 => (x1:Any => Nothing) => eval0(y)(env + (x -> x1))
        case CN(next:CPS[b]) => (x1:Any => b) => evalN(y)(next,env + (x -> x1)) _ // one level lower
      }
      f(k)

    case Reset(x) => 
      evalN(x)(CN(cps),env)(x => k => k(x))(k) // one higher level
  }




  def main(args: Array[String]): Unit = {

    implicit val env = Map[String,EType]()

    typeCheck(Exit(Const(7)), Void)

    typeCheck(If(Const(true),Exit(Const(1)), Exit(Const(0))), Void)

    typeCheck(Let("k", 1, Lam("x", 1, Nat, Exit(Var("x"))),
                  App(Var("k"), Const(3))), Void)


    typeCheck(Reset(Var("x")), List(Unit))(Map("x" -> List(Unit,Unit)))



    // reset { shift(k => k(7)) }

    typeCheck(Reset(Shift(Lam("k",1,Fun(Nat,1,List(Nat)),
                                    App(Var("k"), Const(7))))), List(Nat))


    println(fromScala(q"3"))

    println(pretty(fromScala(q"reset { shift(k => k(1)) } ")))

    def runStd(t: Tree, x: Any) = {
      val p = fromScala(t)
      println(pretty(p))
      val y = evalStd(p) { x => x}
      println(y)
      assert(x == y)
    }

    def runMod(t: Tree, x: Any) = {
      val p = fromScala(t)
      println(pretty(p))
      val y = try eval0(p)//evalMod(p,0)(C0)
      catch {
        case AbortException(a) => a
      }
      println(y)
      assert(x == y)
    }

    runStd(q"reset(shift(k => 1))", 1)
    runStd(q"reset(shift(k => k(1)))", 1)
    runStd(q"reset(shift(k => k(k(1))))", 1)
    runStd(q"reset(shift(k => k(k(k(1)))))", 1)

    runStd(q"reset(2 * shift(k => 1))", 1)
    runStd(q"reset(2 * shift(k => k(1)))", 2)
    runStd(q"reset(2 * shift(k => k(k(1))))", 4)
    runStd(q"reset(2 * shift(k => k(k(k(1)))))", 8)

    runMod(q"exit(reset(2 * shift(k => 1)))", 1)
    runMod(q"exit(reset(2 * shift(k => k(1))))", 2)
    runMod(q"exit(reset(2 * shift(k => k(k(1)))))", 4)
    runMod(q"exit(reset(2 * shift((k: Int => Int) => k(k(k(1))))))", 8)

    runMod(q"exit(1 + shift(k => exit(5)))", 5)
    runMod(q"exit(1 + shift(k => k(1)))", 2)

    runMod(q"exit(reset(1 + reset(2 * shift(k1 => shift(k0 => k0(k1(1)))))))", 3)




    println("DONE")
  }
}