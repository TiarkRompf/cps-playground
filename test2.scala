package test2

// test cases for 0 or 1 return types (undelimited continuations)

/*
TODO: 
  - proper 1st/2nd type checking
  - type-preserving cps
*/

object Test {

  abstract class Term { var tpe: EType = _ }
  abstract class Type

  case class Const(x: Any) extends Term
  case class Var(x: String, n:Int) extends Term
  case class Lam(x: String, n: Int, t: Type, y: Term) extends Term
  case class App(f: Term, x: Term) extends Term
  case class Let(x: String, n: Int, t: Type, y: Term, z: Term) extends Term
  case class If(c: Term, a: Term, b: Term) extends Term
  case class Plus(x: Term, y: Term) extends Term
  case class Times(x: Term, y: Term) extends Term
  case class Reset(x: Term) extends Term
  case class Shift(x: Term) extends Term
  case class Up(x: Term) extends Term
  case class Exit(x: Term) extends Term

  case class ILam(f: Term => Term) extends Term // "administrative" lambda, should inline

  case class Tuple(xs: List[Term]) extends Term
  case class Field(x: Term, y: Int) extends Term


  case object Unknown extends Type
  case object Unit extends Type
  case object Nat extends Type
  case object Bool extends Type
  case class Fun(x: Type, n: Int, y: EType) extends Type
  case class Product(xs: List[Type]) extends Type

  type EType = Option[Type] // None = doesn't return
  val Void = None

  // Note on usage of 'n': 
  // 1 means first class
  // 2 means second class
  // 0 means unknown (e.g. in typeConforms) TODO

  // --------------- type checking ---------------

  implicit class foo(t: Term) {
    def withType(ty: EType) = try t finally t.tpe = ty
  }

  def typeCheck1(t: Term, ty: EType)(implicit env: Map[String,Type]): Term = t match {
    case Const(x: Int) =>       t withType Some(Nat)
    case Const(x: Boolean) =>   t withType Some(Bool)
    case Var(x,n) =>            t withType Some(env(x))

    case Exit(x) =>
      val x1 = typeCheck(x, Some(Nat))
      Exit(x1) withType Void

    case Plus(a, b) =>
      val a1 = typeCheck(a, Some(Nat))
      val b1 = typeCheck(b, Some(Nat))
      Plus(a1, b1) withType Some(Nat)

    case Times(a, b) =>
      val a1 = typeCheck(a, Some(Nat))
      val b1 = typeCheck(b, Some(Nat))
      Times(a1, b1) withType Some(Nat)

    case Let(x,n,t,y,z) =>
      val y1 = typeCheck(y, Some(t))(env + (x -> t))
      val z1 = typeCheck(z, ty)(env + (x -> y1.tpe.get))
      Let(x,n,t,y1,z1) withType z1.tpe

    case If(c,a,b) =>
      val c1 = typeCheck(c, Some(Nat))
      val a1 = typeCheck(a, ty)
      val b1 = typeCheck(b, ty)
      assert(a1.tpe == b1.tpe)
      If(c1,a1,b1) withType a1.tpe

    case App(f, x) => 
      val f1 = typeCheck(f, Some(Fun(Unknown,1,ty)))
      val Some(Fun(ty1,n,ty2)) = f1.tpe
      val x1 = typeCheck(x, Some(ty1))
      App(f1,x1) withType ty2

    case Lam(x, n, t0, y) => 
      ty match {
        case Some(Fun(te, n, ts2)) =>
          val t1 = if (t0 == Unknown) te else t0
          assert(t1 != Unknown,
            s"missing parameter type!\n" +
            s"    expression: "+pretty(t) + "\n" +
            s"    expected:   "+ty.map(pretty).mkString(" / ")
          )
          val y1 = typeCheck(y, ts2)(env + (x -> t1))
          Lam(x, n, t1, y1) withType Some(Fun(t1, n, y1.tpe))
        //case _ => // error
      }

    case Shift(f) =>
      val Some(t1) = ty
      val f1 = typeCheck(f, Some(Fun(Fun(t1,1,Void),1,Void)))
      val Some(Fun(Fun(t2,1,ts2),1,ts3)) = f1.tpe
      assert(typeConformsE(ts2,ts3))
      Shift(f1) withType Some(t2)

  }

  def typeCheck(t: Term, ty: EType)(implicit env: Map[String,Type]): Term = {
    if (t.tpe ne null) return t

    var t1 = typeCheck1(t,ty)

    def assert(b: Boolean, s: String) = if (!b) println(s)

    assert(typeConformsE(t1.tpe, ty), 
      s"type error!\n" +
      s"    expression: "+pretty(t) + "\n" +
      s"    expected:   "+ty.map(pretty).mkString(" / ") + "\n" +
      s"    actual:     "+t1.tpe.map(pretty).mkString(" / ")
    )
    t1
  }

  // check against Unknown
  // check that type includes no Unknown

  def typeConformsE(t1: EType, t2: EType): Boolean = (t1,t2) match {
    case (None, None) => true
    case (Some(t1), Some(t2)) => typeConforms(t1, t2)
  }

  // this is to deal with unknowns -- we're not doing subtyping
  def typeConforms(t1: Type, t2: Type): Boolean = (t1,t2) match {
    case (Nat, Nat) => true
    case (Bool, Bool) => true
    case (Nat, Unknown) => true
    case (Bool, Unknown) => true
    case (Fun(t1,n,t2), Unknown) => typeConforms(t1, Unknown) && typeConformsE(t2, t2.map(_ => Unknown))
    case (Fun(t1,n1,t2), Fun(t3,n2,t4)) => typeConforms(t1, t3) && typeConformsE(t2, t4) && n1 != 0 && (n2 == 0 || n1 == n2)
    case _ => false
  }



  // --------------- parsing (from Scala quasiquotes) ---------------

  import scala.reflect.runtime.universe.{Type => SType, _}
  def fromScala(t: Tree): Term = t match {
    case Literal(Constant(x)) => Const(x)
    case Ident(x) => Var(x.toString,0)
    case q"exit($x)" => Exit(fromScala(x))
    case q"reset($x)" => Reset(fromScala(x))
    case q"shift($x)" => Shift(fromScala(x))
    case q"($x:${t}) => $y" => 
      Lam(x.toString,1,fromScala1(t),fromScala(y))
    case q"$x + $y" => Plus(fromScala(x),fromScala(y))
    case q"$x - $y" => Plus(fromScala(x),Times(Const(-1),fromScala(y)))
    case q"$x * $y" => Times(fromScala(x),fromScala(y))
    case q"val $x:${t} = $y; $z" => Let(x.toString,0,fromScala1(t),fromScala(y),fromScala(z))
    case q"if($c) $a else $b" => If(fromScala(c),fromScala(a),fromScala(b))
    case Apply(f,x::Nil) => App(fromScala(f),fromScala(x))
  }

  def fromScala1(t: Tree): Type = t match {
    case tq"Int" => Nat
    case tq"Nat" => Nat
    case tq"$a => $b" => Fun(fromScala1(a), 1, Some(fromScala1(b)))
    case _ if t.toString == "Any" => Unknown
    case _ if t.toString == "<type ?>" => Unknown
  }

  // --------------- pretty printing ---------------

  def pretty(t: Term): String = t match {
    case Const(x) => x.toString
    case Var(x,n) => x.toString
    case App(f,x) => s"${pretty(f)}(${prettyb(x)})"
    case Lam(x,n,t,y) if t == Unknown => s"($x $n=> ${prettyb(y)})"
    case Lam(x,n,t,y) => s"($x: ${prettyb(t)} $n=> ${prettyb(y)})"
    case Plus(x,y) => s"(${pretty(x)} + ${pretty(y)})"
    case Times(x,y) => s"(${pretty(x)} * ${pretty(y)})"
    case Up(x) => s"up(${prettyb(x)})"
    case Exit(x) => s"exit(${prettyb(x)})"
    case Reset(x) => s"reset(${prettyb(x)})"
    case Shift(x) => s"shift(${prettyb(x)})"
    case ILam(f) => s"(.. => ..)"
    case Tuple(xs) => xs map pretty mkString ","
    case Field(x,n) => s"${pretty(x)}.$n"
    case Let(x,n,t,y,z) if t == Unknown => s"val $x = ${pretty(y)}\n${pretty(z)}"
    case Let(x,n,t,y,z) => s"val $x: ${prettyb(t)} = ${pretty(y)}\n${pretty(z)}"
    case If(c,a,b) => s"if (${pretty(c)}) ${pretty(a)} else ${pretty(b)}"
  }

  def prettyb(t: Term): String = t match {
    case Lam(x,n,t,y) if t == Unknown => s"$x $n=> ${prettyb(y)}"
    case Lam(x,n,t,y) => s"$x: ${prettyb(t)} $n=> ${prettyb(y)}"
    case Plus(x,y) => s"${pretty(x)} + ${pretty(y)}"
    case Times(x,y) => s"${pretty(x)} * ${pretty(y)}"
    case _ => pretty(t)
  }


  def pretty(t: EType): String = t map pretty mkString " / "

  def pretty(t: Type): String = t match {
    case Unknown => "?"
    case Fun(a,n,b) => s"${prettyb(a)} => ${pretty(b)}"
    case _ => t.toString
  }

  def prettyb(t: Type): String = t match {
    case Fun(a,n,b) => s"(${prettyb(a)} => ${pretty(b)})"
    case _ => pretty(t)
  }


  // --------------- default evaluator ---------------

  def evalStd(t: Term)(k: Any => Any)(implicit env: Map[String,Any]): Any = try t match {
    case Const(x: Int) =>       k(x)
    case Const(x: Boolean) =>   k(x)
    case Plus(x,y) =>           evalStd(x) { u => evalStd(y) { v => k(u.asInstanceOf[Int] + v.asInstanceOf[Int]) }}
    case Times(x,y) =>          evalStd(x) { u => evalStd(y) { v => k(u.asInstanceOf[Int] * v.asInstanceOf[Int]) }}
    case Var(x,n) =>            k(env(x))

    case Tuple(xs) =>           def rec(xs: List[Term])(k: List[Any] => Any): Any = xs match {
                                  case Nil => k(Nil)
                                  case x::xs => evalStd(x) { u => rec(xs) { us => k(u::us) }}
                                }
                                rec(xs) { us => k(us) }

    case Field(x,n) =>          evalStd(x) { u => k(u.asInstanceOf[List[Any]](n)) }

    case Lam(x,n,t,y) =>        k((x1:Any) => (k1:Any => Any) => evalStd(y)(k1)(env + (x -> x1))) // same level!

    case App(x,y) =>            evalStd(x) { u => evalStd(y) { v => u.asInstanceOf[Any => (Any => Any) => Any](v)(k) }}

    case Let(x0,n0,t0,Lam(x,n,t,y),z) =>        
                                def f(x1:Any)(k1:Any => Any): Any = {
                                  evalStd(y)(k1)(env + (x0 -> f _) + (x -> x1))
                                }
                                evalStd(z)(k)(env + (x0 -> f _))
    
    case Let(x,n,t,y,z) =>      evalStd(y) { u => evalStd(z)(k)(env + (x -> u)) }

    case If(c,a,b) =>
      evalStd(c) { x => if (x.asInstanceOf[Int] > 0) evalStd(a)(k) else evalStd(b)(k) }
  
    case Shift(x) => //shift((k: T => U) => U): T @cps[U]
      evalStd(x) { f => 
        val f1 = f.asInstanceOf[(Any => Any) => (Any => Any) => Any]
        f1((x:Any) => (k1:Any => Any) => k1(k(x)))(x => x) // same level!
      }

    case Reset(x) => 
      k(evalStd(x)(x => x)) // same level

    case Exit(x) => evalStd(x) { u => u }


  } catch { case e => (println("error: "+pretty(t)+"    "+e)); throw e }

  
  // --------------- transform utils ---------------

  var nNames = 0
  def fresh(s: String) = try Ident(TermName(s+nNames)) finally nNames += 1

  def freshv(s: String) = try Var(s+nNames,0) finally nNames += 1

  def app(x: Term, y: Term) = x match {
    case ILam(f) => f(y)
    case _ => App(x,proper(y))
  }

  def proper(f: Term): Term = f match {
    case ILam(f) => setN(fun(f), 1) // mark autogenerated functions (n = 1)
    case Tuple(xs) => Tuple(xs map proper)
    case _ => f
  }

  def ifun(f: Term => Term): Term = ILam(f)

  def field(x: Term, n: Int): Term = x match {
    case Tuple(xs) => xs(n)
    case _ => Field(x,n)
  }

  def explode(f: (Term, Term) => Term)(x: Term): Term = f(field(x,0),field(x,1))
  def explode(f: (Term, Term, Term) => Term)(x: Term): Term = f(field(x,0),field(x,1),field(x,2))
  def explode(f: (Term, Term, Term, Term) => Term)(x: Term): Term = f(field(x,0),field(x,1),field(x,2),field(x,3))

  def fun(f: Term => Term): Term = {
      val z = freshv("z")
      Lam(z.x,0,Unknown,proper(f(z))) // mark proper functions (n = 0) XXX for now assume their args don't escape
  }


  def ifun(f: (Term, Term) => Term): Term = ifun(explode(f)_)
  def ifun(f: (Term, Term, Term) => Term): Term = ifun(explode(f)_)


  def fun(f: (Term, Term) => Term): Term = fun(explode(f)_)
  def fun(f: (Term, Term, Term) => Term): Term = fun(explode(f)_)
  def fun(f: (Term, Term, Term, Term) => Term): Term = fun(explode(f)_)

  def app(f: Term, x: Term, y: Term): Term = app(f, Tuple(List(x,y)))
  def app(f: Term, x: Term, y: Term, z: Term): Term = app(f, Tuple(List(x,y,z)))
  def app(f: Term, x: Term, y: Term, z: Term, u: Term): Term = app(f, Tuple(List(x,y,z,u)))

  def setN(f: Term, n: Int) = f match {
    case Lam(x,n0,t,y) => Lam(x,n,t,y)
    case _ => f
  }

  // --------------- selective cps transform ---------------

  def transTrivial(t: Term)(env: Map[String,Term]): Term = t match {
    case Const(x: Int) =>       ifun(k => app(k, (Const(x))))
    case Const(x: Boolean) =>   ifun(k => app(k, (Const(x))))
    case Plus(x,y) =>           ifun(k => app(transTrivial(x)(env), ifun { u => app(transTrivial(y)(env), ifun { v => app(k, Plus(u,v)) })}))
    case Times(x,y) =>          ifun(k => app(transTrivial(x)(env), ifun { u => app(transTrivial(y)(env), ifun { v => app(k, Times(u,v)) })}))
    case Var(x,n) =>            ifun(k => app(k, (env(x))))

    case Exit(x) =>             app(transTrivial(x)(env), ifun(x => Exit(x)))

    case Lam(x,n,tp,y) =>
      val Some(Fun(t1,_,ts2)) = t.tpe
      if (ts2 == Void)
        ifun(k => app(k, fun(x1 => transTrivial(y)(env + (x -> x1))))) // do not cps transform!
      else 
        ifun(k => app(k, fun((x1,k1) => app(transTrivial(y)(env + (x -> x1)), k1))))

    case App(x,y) =>
      if (t.tpe == Void)
        app(transTrivial(x)(env), ifun { u => app(transTrivial(y)(env), ifun { v => app(u,v) })})
      else
        ifun(k => app(transTrivial(x)(env), ifun { u => app(transTrivial(y)(env), ifun { v => app(u,v,k) })}))

    case Let(x,n,tp, y, z) =>
      if (t.tpe == Void)
        Let(x,n,Unknown, 
          app(transTrivial(y)(env + (x -> Var(x,n))), ifun { u => u }), // XXX: assume this is a lambda ...
          transTrivial(z)(env + (x -> Var(x,n))) )
      else
        ifun(k => 
          Let(x,n,Unknown, 
            app(transTrivial(y)(env + (x -> Var(x,n))), ifun { u => u }), // XXX: assume this is a lambda ...
            app(transTrivial(z)(env + (x -> Var(x,n))), k) ))

    case If(c,a,b) =>
      if (t.tpe == Void) 
        app(transTrivial(c)(env), ifun { c2 =>
          val ift = setN(fun(x => transTrivial(a)(env)), 3)
          val iff = setN(fun(x => transTrivial(b)(env)), 3)
          app(If(c2, ift, iff), Tuple(Nil)) })
      else
        ifun { k0 =>
          app(transTrivial(c)(env), ifun { c2 =>
            val k = setN(proper(k0), 3) // XXX TODO: let bind?
            val ift = setN(fun(x => app(transTrivial(a)(env),k)), 3)
            val iff = setN(fun(x => app(transTrivial(b)(env),k)), 3)
            app(If(c2, ift, iff), Tuple(Nil)) })
        }

    case Shift(f) =>
      ifun(k => 
        app(transTrivial(f)(env), ifun { f1 => 
          app(f1, k)
      }))

  }


  // --------------- low-level evaluator (explicit call stack) ---------------

  def evalLLP(t: Term): Any = {
    var fs = Map[String,Any]()
    var mem = new Array[Any](1000)
    var fp = 100 // start of stack frame
    var ap = 100
    var sp = 101
    var hp = 500

    mem(99) = 1 // we use this as empty tuple (size 1 incl length)

    val exit = (x: Any) => return x

    case class Clos(f: Lam, sp1: Int, e: Map[String,Int])

    /*@scala.annotation.tailrec*/ def evalLLS(t: Term)(implicit env: Map[String,Int]): Any = t match {
      case Let(x1,n1,t1,y,z) => 
        val sp1 = sp; sp+=1
        mem(sp1) = evalLLE(y)(env + (x1 -> sp1))
        println(s"  let $x1 = ${pretty(y)}")
        println(s"    mem($sp1) = ${mem(sp1)}")
        evalLLS(z)(env + (x1 -> sp1))
      case App(f,x) =>
        val f1 = evalLLE(f)
        val x1 = evalLLE(x)
        println(s"  ${pretty(t)}")
        //f1.asInstanceOf[() => Any]()

        {
          val Clos(Lam(x,n,t,y),sp1,env) = f1
          if (n != 0) // reset sp if arg escape (continuation call!) FIXME: should decide based on type!
            sp = sp1
          mem(sp) = x1; sp += 1
          println(s"    mem(${sp-1}) = ${mem(sp-1)}")
          evalLLS(y)(env + (x -> (sp-1)))
        }
      case Exit(x) =>
        evalLLE(x)
    }

    def evalLLE(t: Term)(implicit env: Map[String,Int]): Any = t match {
      case Const(x) => x
      case Var(x,n) => mem(env(x))

      case Times(x,y) =>
        evalLLE(x).asInstanceOf[Int] *
        evalLLE(y).asInstanceOf[Int]

      case Plus(x,y) =>
        evalLLE(x).asInstanceOf[Int] +
        evalLLE(y).asInstanceOf[Int]

      case If(c,a,b) =>
        val c1 = evalLLE(c)
        if (c1.asInstanceOf[Int] > 0)
          evalLLE(a)
        else
          evalLLE(b)

      case Field(x,n) =>     
        evalLLE(x).asInstanceOf[List[Any]](n)

      case Tuple(xs) =>
        xs.map(evalLLE)

      case l@Lam(x,n,t,y) =>
        Clos(l,sp,env)
    }

    evalLLS(t)(Map())

  }



  def main(args: Array[String]): Unit = {

    def genMod3(t: Tree, x: Any) = {
      println("")

      nNames = 0
      val p = fromScala(t)
      println(pretty(p))
      val p1 = typeCheck(p,Void)(Map())
      println(pretty(p1))

      {nNames = 0
      val y = transTrivial(p1)(Map())
      println(" "+pretty(y))
      val z = evalStd(y) { x => x} (Map())
      println(" "+z)
      assert(x == z)}

      {nNames = 0
      val y = transTrivial(p1)(Map())
      println(" "+pretty(y))
      val z = evalLLP(y)
      println(" "+z)
      assert(x == z)}
    }



    println("--- mod2 gen ---")

    genMod3(q"exit(((x:Nat) => 2 * x)(1))", 2)

    genMod3(q"val fac: (Nat => Nat) = n => if (n) fac(n-1) else 0; exit(fac(4))", 0)


    genMod3(q"val fac: (Nat => Nat) = n => if (n) n * fac(n-1) else 1; exit(fac(4))", 24)

    genMod3(q"val fib: (Nat => Nat) = n => if (n-1) fib(n-1)+fib(n-2) else 1; exit(fib(5))", 8)


    println("DONE")
  }
}