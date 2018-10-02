package test1

object Test {

  abstract class Term { var tpe: EType = _ }
  abstract class Type

  case class Const(x: Any) extends Term
  case class Var(x: String) extends Term
  case class Lam(x: String, n: Int, t: Type, y: Term) extends Term
  case class App(f: Term, x: Term) extends Term
  case class Let(x: String, n: Int, y: Term, z: Term) extends Term
  case class If(c: Term, a: Term, b: Term) extends Term
  case class Plus(x: Term, y: Term) extends Term
  case class Times(x: Term, y: Term) extends Term
  case class Reset(x: Term) extends Term
  case class Shift(x: Term) extends Term
  case class Up(x: Term) extends Term
  case class Exit(x: Term) extends Term

  case class ILam(f: Term => Term) extends Term

  case class Tuple(xs: List[Term]) extends Term
  case class Field(x: Term, y: Int) extends Term


  case object Unknown extends Type
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

  implicit class foo(t: Term) {
    def withType(ty: EType) = try t finally t.tpe = ty
  }

  def typeInfer(t: Term)(implicit env: Map[String,EType]): Term = {
    t withType typeInfer1(t)
  }

  def typeInfer1(t: Term)(implicit env: Map[String,EType]): EType = t match {
    case Const(x: Int) =>       List(Nat)
    case Const(x: Boolean) =>   List(Bool)
    case Var(x) =>              env(x)
    case Exit(x) =>
      typeCheck(x, List(Nat))
      Void
    case If(c,a,b) =>
      val e1 = typeCheckPrefix(c, List(Bool)) // may effect
      val ty = typeInfer(a).tpe
      typeCheck(b, ty)
      seq(e1,ty)
    case Let(x, n, y, z) => 
      val ty = typeInfer(y).tpe
      val ty1 = typeInfer(z)(env + (x -> List(ty.head))).tpe
      seq(ty,ty1)
    case Lam(x, n, t, y) => 
      val ty = typeInfer(y)(env + (x -> List(t))).tpe
      List(Fun(t, n, ty))
    case App(f, x) => 
      val tf @ (Fun(thx,n,ty)::_) = typeInfer(f).tpe
      val tx = typeCheckPrefix(x, List(thx))
      seq(seq(tf,tx),ty)

    case Reset(x) => //reset(T @cps[T]): T
      val thd::ttl = typeInfer(x).tpe
      assert(thd == ttl.head)
      ttl

    case Shift(x) => //shift((k: T => U) => U): T @cps[U]
      val tf @ (Fun(Fun(tx,n1,tu1),n2,tu2)::Nil) = typeInfer(x).tpe
      assert(tu1 == tu2)
      tx::tu1
  }

  def typeCheckPrefix(t: Term, ty: EType)(implicit env: Map[String,EType]): EType = (t,ty) match {
    case (_,_) =>
      val ty1 = typeInfer(t).tpe
      assert(ty1 startsWith ty)
      ty1
  }

  def typeCheckA(t: Term, ty: EType)(implicit env: Map[String,EType]): Term = (t,ty) match {
    case (_,_) =>
      assert(typeInfer(t).tpe == ty)
      t
  }

  def comb(t1: EType, t2: EType): EType = (t1,t2) match {
    case (_,Nil) => t1
    case (Nil,_) => t2
    case (a1::as1,b1::bs1) if a1 == b1 => a1::comb(as1,bs1)
    case _ => assert(false, "incompatible context types " + t1.map(pretty).mkString(" / ") + 
      " and " + t2.map(pretty).mkString(" / "))
      ???
  }

  // The assigned type needs to combine effect information from all subexpressions.
  // It's OK if 
  def typeCheck1(t: Term, ty: EType)(implicit env: Map[String,EType]): Term = t match {
    case Const(x: Int) =>       t withType List(Nat)
    case Const(x: Boolean) =>   t withType List(Bool)
    case Var(x) =>              t withType env(x)

    case Up(x) =>
      val x1 = typeCheck(x, ty.init)
      Up(x1) withType (x1.tpe :+ ty.last)

    case Exit(x) =>
      val x1 = typeCheck(x, List(Nat))
      Exit(x1) withType Void

    case Plus(a, b) =>
      // need to deal with 2 * shift() and shift() * 2
      val a1 = typeCheck(a, Nat::ty.tail) // 
      val b1 = typeCheck(b, Nat::ty.tail)
      Plus(a1, b1) withType Nat::comb(a1.tpe.tail, b1.tpe.tail)

    case Times(a, b) =>
      // need to deal with 2 * shift() and shift() * 2
      val a1 = typeCheck(a, Nat::ty.tail) // 
      val b1 = typeCheck(b, Nat::ty.tail)
      Times(a1, b1) withType Nat::comb(a1.tpe.tail, b1.tpe.tail)

    case App(f, x) => 
      if (ty == Nil) {
        // TODO: check this
        val f1 = typeCheck(f, Fun(Unknown,1,ty)::Nil)
        val Fun(ty1,n,ty2)::Nil = f1.tpe
        val x1 = typeCheck(x, ty1::Nil)
        App(f1,x1) withType ty2
      } else {
        val f1 = typeCheck(f, Fun(Unknown,1,ty)::ty.tail)
        val Fun(ty1,n,ty2)::_ = f1.tpe
        val x1 = typeCheck(x, ty1::ty.tail)
        App(f1,x1) withType comb(comb(f1.tpe.tail, x1.tpe.tail), ty2)
      }

    case Lam(x, n, t0, y) => 
      ty match {
        case Fun(te, n, ts2)::_ =>
          val t1 = if (t0 == Unknown) te else t0
          assert(t1 != Unknown,
            s"missing parameter type!\n" +
            s"    expression: "+pretty(t) + "\n" +
            s"    expected:   "+ty.map(pretty).mkString(" / ")
          )
          val y1 = typeCheck(y, ts2)(env + (x -> List(t1)))
          // TODO: insert up if not enough types?
          Lam(x, n, t1, y1) withType List(Fun(t1, n, y1.tpe))
        //case _ => // error
      }

    case Shift(f) => //shift((k: T => U) => U): T @cps[U]
      val t1::ts1 = ty
      val f1 = typeCheck(f, Fun(Fun(t1,1,ts1),1,ts1)::ts1)
      val Fun(Fun(t2,1,ts2),1,ts3)::_ = f1.tpe
      assert(typeConformsE(ts2,ts3))
      Shift(f1) withType (t2::ts2)

    case Reset(x) => 
      val x1 = typeCheck(x, ty.head::ty)
      assert(x1.tpe.length < 2 || x1.tpe.head == x1.tpe.tail.head)
      // TODO: insert up if not enough types?
      if (x1.tpe.length < 2)
        Reset(x1) withType x1.tpe
      else
        Reset(x1) withType x1.tpe.tail
  }

  def typeCheck(t: Term, ty: EType)(implicit env: Map[String,EType]): Term = {
    if (t.tpe ne null) return t

    var t1 = typeCheck1(t,ty)
    //while (t1.tpe.length < ty.length) // context polymorphism -- try to adapt
      //t1 = typeCheck1(Up(t1),ty)

    def assert(b: Boolean, s: String) = if (!b) println(s)

    assert(typeConformsEpartial(t1.tpe, ty), 
      s"type error!\n" +
      s"    expression: "+pretty(t) + "\n" +
      s"    expected:   "+ty.map(pretty).mkString(" / ") + "\n" +
      s"    actual:     "+t1.tpe.map(pretty).mkString(" / ")
    )
    t1
  }

  // check against Unknown
  // check that type includes no Unknown

  def typeConformsE(t1: EType, t2: EType): Boolean = 
    t1.length == t2.length && ((t1 zip t2) forall (typeConforms _).tupled)

  def typeConformsEpartial(t1: EType, t2: EType): Boolean = 
    t1.length <= t2.length && ((t1 zip t2) forall (typeConforms _).tupled)

  // this is to deal with unknowns -- we're not doing subtyping
  def typeConforms(t1: Type, t2: Type): Boolean = (t1,t2) match {
    case (Nat, Nat) => true
    case (Bool, Bool) => true
    case (Nat, Unknown) => true
    case (Bool, Unknown) => true
    case (Fun(t1,n,t2), Unknown) => typeConforms(t1, Unknown) && typeConformsE(t2, t2.map(_ => Unknown))
    case (Fun(t1,n1,t2), Fun(t3,n2,t4)) => n1 == n2 && typeConforms(t1, t3) && typeConformsE(t2, t4)
    case _ => false
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
    case tq"Nat" => Nat
    case tq"$a => $b" => Fun(fromScala1(a), 1, fromScala1(b)::Nil)
    case _ if t.toString == "Any" => Unknown
    case _ if t.toString == "<type ?>" => Unknown
  }


  def pretty(t: Term): String = t match {
    case Const(x) => x.toString
    case Var(x) => x.toString
    case App(f,x) => s"${pretty(f)}(${prettyb(x)})"
    case Lam(x,n,t,y) if t == Unknown => s"($x => ${prettyb(y)})"
    case Lam(x,n,t,y) => s"($x: ${prettyb(t)} => ${prettyb(y)})"
    case Plus(x,y) => s"(${pretty(x)} + ${pretty(y)})"
    case Times(x,y) => s"(${pretty(x)} * ${pretty(y)})"
    case Up(x) => s"up(${prettyb(x)})"
    case Exit(x) => s"exit(${prettyb(x)})"
    case Reset(x) => s"reset(${prettyb(x)})"
    case Shift(x) => s"shift(${prettyb(x)})"
    case ILam(f) => s"(.. => ..)"
    case Tuple(xs) => xs map pretty mkString ","
    case Field(x,n) => s"${pretty(x)}.$n"
  }

  def prettyb(t: Term): String = t match {
    case Lam(x,n,t,y) if t == Unknown => s"$x => ${prettyb(y)}"
    case Lam(x,n,t,y) => s"$x: ${prettyb(t)} => ${prettyb(y)}"
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


  def evalStd(t: Term)(k: Any => Any)(implicit env: Map[String,Any]): Any = t match {
    case Const(x: Int) =>       k(x)
    case Const(x: Boolean) =>   k(x)
    case Plus(x,y) =>           evalStd(x) { u => evalStd(y) { v => k(u.asInstanceOf[Int] + v.asInstanceOf[Int]) }}
    case Times(x,y) =>          evalStd(x) { u => evalStd(y) { v => k(u.asInstanceOf[Int] * v.asInstanceOf[Int]) }}
    case Var(x) =>              k(env(x))

    case Tuple(List(x,y)) =>    evalStd(x) { u => evalStd(y) { v => k(List(u,v)) }}
    case Tuple(List(x,y,z)) =>  evalStd(x) { u => evalStd(y) { v => evalStd(z) { w => k(List(u,v,w)) }}}
    case Tuple(List(x,y,z,a)) =>evalStd(x) { u => evalStd(y) { v => evalStd(z) { w => evalStd(a) { d => k(List(u,v,w,d)) }}}}
    case Field(x,n) =>          evalStd(x) { u => k(u.asInstanceOf[List[Any]](n)) }

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

    case Exit(x) => evalStd(x) { u => u }
  }

  var nNames = 0
  def fresh(s: String) = try Ident(TermName(s+nNames)) finally nNames += 1

  def transStd(t: Term)(k: Tree => Tree)(implicit env: Map[String,Tree]): Tree = t match {
    case Const(x: Int) =>       k(Literal(Constant(x)))
    case Const(x: Boolean) =>   k(Literal(Constant(x)))
    case Plus(x,y) =>           transStd(x) { u => transStd(y) { v => k(q"$u + $v") }}
    case Times(x,y) =>          transStd(x) { u => transStd(y) { v => k(q"$u * $v") }}
    case Var(x) =>              k(q"${env(x)}")

    case Lam(x,n,t,y) =>
      val (x1,k1) = (fresh("x"),fresh("k"))
      val k1f = (x: Tree) => q"$k1($x)" // eta
      k(q"(($x1:Any) => ($k1:Any) => ${ transStd(y)(k1f)(env + (x -> x1)) })")

    case App(x,y) =>
      val z = fresh("z")
      val ks = q"(($z:Any) => ${k(q"$z")})"
      transStd(x) { u => transStd(y) { v => q"$u($v)($ks)" }}

    case If(c,a,b) =>
      transStd(c) { x => if (x.asInstanceOf[Boolean]) transStd(a)(k) else transStd(b)(k) }
  
    case Shift(Lam(x,n,t,y)) =>
      val k1 = fresh("k")
      val (zz,kk) = (fresh("zz"),fresh("kk"))
      val ks = q"(($zz:Any) => ($kk:Any) => $kk(${k(q"$zz")}))" // eta, delimited (caller expects to pass cont)
      q"(($k1:Any) => ${ transStd(y)(x => x)(env + (x -> k1)) })($ks)"


    case Shift(x) => //shift((k: T => U) => U): T @cps[U]
      transStd(x) { f => 
        val x = fresh("x")
        val (zz,kk) = (fresh("zz"),fresh("kk"))
        q"$f(($zz:Any) => ($kk:Any) => $kk(${k(q"$zz")}))($x => $x)"
      }

    case Reset(x) => 
      k(transStd(x)(x => x)) // same level

  }


  case class AbortException(x: Any) extends Exception

  def eval0[A](t: Term)(implicit env: Map[String,Any]): A = t match {
    case Exit(x) =>
      evalN[A](x)(C0(),env) { x => throw AbortException(x) }
    // case If(c,a,b) =>
    //   if (eval1(c).asInstanceOf[Boolean]) eval0(a) else eval0(b)
    // case Let(x, n, y, z) => 
    //   val v = eval1(y)
    //   eval0(z)(env + (x -> v))
    case App(f, x) => 
      evalN[A](f)(C0(),env) { fv =>
      evalN[A](x)(C0(),env) { fx =>
      fv.asInstanceOf[Any=>A](fx) }}
  }


  type Wrap[A] = (Any => A) => A

  abstract class CPS[A]
  case class C0[A]() extends CPS[A]
  case class CN[A](next: CPS[A]) extends CPS[Wrap[A]]


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
        case _:C0[a]  => (x1:Any => a) => eval0(y)(env + (x -> x1))
        case CN(next:CPS[b]) => (x1:Any => b) => evalN(y)(next,env + (x -> x1)) _ // one level lower
      }
      f(k)

    case Reset(x) => 
      evalN(x)(CN(cps),env)(x => k => k(x))(k) // one higher level
  }



  def trans0(t: Term)(implicit env: Map[String,Tree]): Tree = t match {
    case Exit(x) =>
      transN[Tree](x)(C0(),env) { x => q"exit($x)" }
    // case If(c,a,b) =>
    //   if (eval1(c).asInstanceOf[Boolean]) eval0(a) else eval0(b)
    // case Let(x, n, y, z) => 
    //   val v = eval1(y)
    //   eval0(z)(env + (x -> v))
    case App(f, x) => 
      transN[Tree](f)(C0(),env) { fv =>
      transN[Tree](x)(C0(),env) { fx =>
      q"$fv($fx)" }}
  }

  case class Eta(f: Tree) extends (Tree => Tree) {
    def apply(x: Tree) = q"$f($x)"
  }

  def eta(f: Tree => Tree): Tree = f match {
    case Eta(f) => f
    case _ =>
      val z = fresh("z")
      q"(($z:Any) => ${f(q"$z")})"
  }


  // why does this work?
  // a single continuation is enough to CPS transform, the result in general is
  // a lambda that expects further continuations (just like nested monads)
  // type T becomes (T => Void) => Void
  // or (T => (U => Void) => Void) => (U => Void) => Void   =   (T => A) => A 
  def transN[A](t: Term)(cps: CPS[A], env: Map[String,Tree])(k: Tree => Tree): Tree = t match {
    case Const(x: Int) =>       k(Literal(Constant(x)))
    case Const(x: Boolean) =>   k(Literal(Constant(x)))
    case Plus(x,y) =>           transN(x)(cps,env) { u => transN(y)(cps,env) { v => k(q"$u + $v") }}
    case Times(x,y) =>          transN(x)(cps,env) { u => transN(y)(cps,env) { v => k(q"$u * $v") }}
    case Var(x) =>              k(q"${env(x)}")

    case Lam(x,n,tp,y) if t.tpe ne null =>
      val Fun(t1,_,ts2)::rest = t.tpe
      val (x1,k1) = (fresh("x"),fresh("k"))
      if (ts2.length > 0)
        k(q"(($x1:Any) => ($k1:Any) => ${ transN(y)(cps,env + (x -> x1))(Eta(k1)) })")
      else
        k(q"(($x1:Any) => ${ trans0(y)(env + (x -> x1)) })")

      // as many continuations as necessary??

    case Lam(x,n,t,y) =>        
      val (x1,k1) = (fresh("x"),fresh("k"))
      k(q"(($x1:Any) => ($k1:Any) => ${ transN(y)(cps,env + (x -> x1))(Eta(k1)) })")
      // as many continuations as necessary??

    case App(x,y) =>            
      val ks = eta(k)
      transN(x)(cps,env) { u => transN(y)(cps,env) { v => q"$u($v)($ks)" }}

    case If(c,a,b) =>
      transN(c)(cps,env) { x => if (x.asInstanceOf[Boolean]) transN(a)(cps,env)(k) else transN(b)(cps,env)(k) }
  
    case Up(x) => 
      transN(x)(cps,env)(k) // XXX no-op here -- wasn't needed

    case Shift(f) if f.tpe ne null => //shift((k: T => U) => U): T @cps[U]
      transN[A](f)(cps,env) { f1 =>
        val ks = eta(k)
        q"$f1($ks)"
      }

    case Shift(Lam(x,n,t,y)) => //shift((k: T => U) => U): T @cps[U]

      cps match {  // one level lower
        case _:C0[a] =>

          val k1 = fresh("k")

          val ks = eta(k) // eta, delimited (caller *does not* expect to pass cont)

          val body = q"(($k1:Any) => ${ trans0(y)(env + (x -> k1)) })"

          q"$body($ks)"

       case CN(next:CPS[b]) => 

          val k1 = fresh("k")
          val kk = fresh("kk")

          val ks = eta(k) // eta, delimited (caller expects to pass cont, could eta one more!)

          val body = q"(($k1:Any) => ($kk:Any) => ${ transN(y)(next,env + (x -> k1))(Eta(kk)) })"

          q"$body($ks)"
      }


    case Reset(x) => 
      val k1 = fresh("k")
      val ks = eta(k)

      q"${ (transN(x)(CN(cps),env)(x => q"(($k1: Any) => $k1($x))")) } ($ks)" // one level higher
  }


  def freshv(s: String) = try Var(s+nNames) finally nNames += 1

  def app(x: Term, y: Term) = x match {
    case ILam(f) => f(y)
    case _ => App(x,proper(y))
  }

  def proper(f: Term): Term = f match {
    case ILam(f) => fun(f)
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
      Lam(z.x,1,Unknown,proper(f(z)))
  }


  def ifun(f: (Term, Term) => Term): Term = ifun(explode(f)_)
  def ifun(f: (Term, Term, Term) => Term): Term = ifun(explode(f)_)


  def fun(f: (Term, Term) => Term): Term = fun(explode(f)_)
  def fun(f: (Term, Term, Term) => Term): Term = fun(explode(f)_)
  def fun(f: (Term, Term, Term, Term) => Term): Term = fun(explode(f)_)

  def app(f: Term, x: Term, y: Term): Term = app(f, Tuple(List(x,y)))
  def app(f: Term, x: Term, y: Term, z: Term): Term = app(f, Tuple(List(x,y,z)))
  def app(f: Term, x: Term, y: Term, z: Term, u: Term): Term = app(f, Tuple(List(x,y,z,u)))


  // note: without eta in Lam case, result is identical to transN above
  def transTrivial(t: Term)(env: Map[String,Term]): Term = t match {
    case Const(x: Int) =>       ifun(k => app(k, (Const(x))))
    case Const(x: Boolean) =>   ifun(k => app(k, (Const(x))))
    case Plus(x,y) =>           ifun(k => app(transTrivial(x)(env), ifun { u => app(transTrivial(y)(env), ifun { v => app(k, Plus(u,v)) })}))
    case Times(x,y) =>          ifun(k => app(transTrivial(x)(env), ifun { u => app(transTrivial(y)(env), ifun { v => app(k, Times(u,v)) })}))
    case Var(x) =>              ifun(k => app(k, (env(x))))

    case Exit(x) =>             app(transTrivial(x)(env), ifun(x => Exit(x)))

    case Lam(x,n,tp,y) =>
      val Fun(t1,_,ts2)::rest = t.tpe
      if (ts2.length > 0) {
        def eta(n: Int, x: Term): Term = x // optional!!
          //if (n > 0) fun(k => app(eta(n-1,x),k)) else x
        ifun(k => app(k, fun(x1 => eta(ts2.length, transTrivial(y)(env + (x -> x1))))))
      }
      else 
        ifun(k => app(k, fun(x1 => transTrivial(y)(env + (x -> x1))))) // do not cps transform!

    case App(x,y) =>
      if (t.tpe.length == 0)
        app(transTrivial(x)(env), ifun { u => app(transTrivial(y)(env), ifun { v => app(u,v) })})
      else
        ifun(k => app(transTrivial(x)(env), ifun { u => app(transTrivial(y)(env), ifun { v => app(app(u,v),k) })}))

    // case If(c,a,b) =>
    //   transN(c)(cps,env) { x => if (x.asInstanceOf[Boolean]) transN(a)(cps,env)(k) else transN(b)(cps,env)(k) }
  
    // case Up(x) => 
    //   transN(x)(cps,env)(k) // XXX no-op here -- wasn't needed

    case Shift(f) => //shift((k: T => U) => U): T @cps[U]
      ifun(k => 
        app(transTrivial(f)(env), ifun { f1 => // multiple continuations, turn them into one passes to f
          app(f1, k)
      }))

    case Reset(x) => 
      val id1 = ifun(x => ifun(k => app(k,x)))
      app(transTrivial(x)(env), id1)
      // one level higher: result expects to be called with k!
      // fun(k => app(..., k))
  }


  def transFullEta(t: Term)(env: Map[String,Term]): Term = t match {
    case Const(x: Int) =>       ifun(k => app(k, (Const(x))))
    case Const(x: Boolean) =>   ifun(k => app(k, (Const(x))))
    case Plus(x,y)  if x.tpe.length == 1 && y.tpe.length == 1 =>
                                ifun(k => app(transFullEta(x)(env), ifun { u => app(transFullEta(y)(env), ifun { v => app(k, Plus(u,v)) })}))

    case Plus(x,y) if x.tpe.length == 1 && y.tpe.length == 2 =>
      ifun((k1,k2) => 
        app(transFullEta(x)(env), ifun { u => 
          app(transFullEta(y)(env), ifun { (v,vk) => 
            app(k1, Plus(u,v), vk) }, k2)}))


    case Times(x,y) if x.tpe.length == 1 && y.tpe.length == 1 =>
                                ifun(k => app(transFullEta(x)(env), ifun { u => app(transFullEta(y)(env), ifun { v => app(k, Times(u,v)) })}))

    case Times(x,y) if x.tpe.length == 1 && y.tpe.length == 2 =>
      ifun((k1,k2) => 
        app(transFullEta(x)(env), ifun { u => 
          app(transFullEta(y)(env), ifun { (v,vk) => 
            app(k1, Times(u,v), vk) }, k2)}))

    case Times(x,y) if x.tpe.length == 1 && y.tpe.length == 3 =>
      ifun((k1,k2,k3) => 
        app(transFullEta(x)(env), ifun { u => 
          app(transFullEta(y)(env), ifun { (v,vk2,vk3) => 
            app(k1, Times(u,v), vk2, vk3) }, k2, k3)}))

    case Var(x) =>              ifun(k => app(k, (env(x))))

    case Exit(x) =>             app(transFullEta(x)(env), ifun(x => Exit(x)))

    case Lam(x,n,tp,y) =>
      val Fun(t1,_,ts2)::rest = t.tpe
      ts2.length match {
        case 0 =>
          ifun(k => app(k, fun(x1 => transFullEta(y)(env + (x -> x1))))) // do not cps transform!
        case 1 =>
          ifun(k => app(k, fun((x1,k1) => app(transFullEta(y)(env + (x -> x1)), k1)))) // XXX app with k1 ok? assume suitably expanded ...
        case 2 =>
          ifun(k => app(k, fun((x1,k1,k2) => app(transFullEta(y)(env + (x -> x1)), k1, k2))))
        case 3 =>
          ifun(k => app(k, fun((x1,k1,k2,k3) => app(transFullEta(y)(env + (x -> x1)), k1, k2, k3))))
      }

    case App(x,y) =>
      t.tpe.length match {
        case 0 =>
          app(transFullEta(x)(env), ifun { u => app(transFullEta(y)(env), ifun { v => app(u,v) })})
        case 1 =>
          ifun(k => app(transFullEta(x)(env), ifun { u => app(transFullEta(y)(env), ifun { v => app(u,v,k) })}))
        case 2 =>
          // ifun(k1 => ifun(k2 => app(transFullEta(x)(env), ifun { u => app(transFullEta(y)(env), ifun { v => app(app(app(u,v),k1),k2) })})))

          assert(x.tpe.length == 1)
          assert(y.tpe.length == 2)

          ifun((k1,k2) => 
            app(transFullEta(x)(env), ifun { u => 
              app(transFullEta(y)(env), ifun { (v,vk) => app(u,v,k1,vk) }, k2)}
            ))

        case 3 =>
          assert(x.tpe.length == 1)
          assert(y.tpe.length == 1)
          ifun((k1,k2,k3) =>
            app(transFullEta(x)(env), ifun { u => 
              app(transFullEta(y)(env), ifun { v => 
                app(u,v,k1,k2,k3) })}))
      }

    // case If(c,a,b) =>
    //   transN(c)(cps,env) { x => if (x.asInstanceOf[Boolean]) transN(a)(cps,env)(k) else transN(b)(cps,env)(k) }
  
    // case Up(x) => 
    //   transN(x)(cps,env)(k) // XXX no-op here -- wasn't needed

    case Shift(f) => //shift((k: T => U) => U): T @cps[U]
      assert(f.tpe.length == 1)
      t.tpe.length match {
        case 1 =>
          ifun(k => 
            app(transFullEta(f)(env), ifun { f1 => // assume f has level 1
              app(f1, k)
          }))
        case 2 =>
          ifun((k1,k2) => 
            app(transFullEta(f)(env), ifun { f1 => // assume f has level 1
              app(f1,k1,k2)
          }))
        case 3 =>
          ifun((k1,k2,k3) => 
            app(transFullEta(f)(env), ifun { f1 => // assume f has level 1
              app(f1,k1,k2,k3)
          }))
      }  

    case Reset(x) if x.tpe.length == t.tpe.length => // special case
      assert(x.tpe.length == 1)
      transFullEta(x)(env)

    case Reset(x) =>
      assert(x.tpe.length == t.tpe.length + 1)
      t.tpe.length match {
        case 1 =>
          val id1 = ifun((x,k) => app(k,x))
          ifun(k => app(transFullEta(x)(env), id1, k))
        case 2 =>
          val id2 = ifun((x,k1,k2) => app(k1,x,k2))
          ifun((k1,k2) => app(transFullEta(x)(env), id2, k1, k2))
      }
      // one level higher: result expects to be called with k!
      // fun(k => app(..., k))
  }



//(z0 => z1 => (z2 => z3 => (z4 => z5 => z4(z0)(z5))(z6 => z2(z6)(z3)))(z1))(1)(z7 => z8 => z8(2 * z7))(z9 => z10 => z10(1 + z9))(z11 => exit(z11))



  def main(args: Array[String]): Unit = {

    implicit val env = Map[String,EType]()

    typeCheckA(Exit(Const(7)), Void)

    typeCheckA(If(Const(true),Exit(Const(1)), Exit(Const(0))), Void)

    typeCheckA(Let("k", 1, Lam("x", 1, Nat, Exit(Var("x"))),
                  App(Var("k"), Const(3))), Void)


    typeCheckA(Reset(Var("x")), List(Unit))(Map("x" -> List(Unit,Unit)))



    // reset { shift(k => k(7)) }

    typeCheckA(Reset(Shift(Lam("k",1,Fun(Nat,1,List(Nat)),
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

    def genStd(t: Tree, x: Any) = {
      nNames = 0
      val p = fromScala(t)
      println(pretty(p))
      val ys = transStd(p) { x => x} (Map())
      //println(y)
      val y = fromScala(ys)
      println(pretty(y))
      val z = evalStd(y) { x => x}
      println(z)
      assert(x == z)
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

    def genMod(t: Tree, x: Any) = {
      nNames = 0
      val p = fromScala(t)
      println(pretty(p))
      val ys = try trans0(p)(Map())//evalMod(p,0)(C0)
      val y = fromScala(ys)
      println(pretty(y))
      val z = evalStd(y) { x => x}
      println(z)
      assert(x == z)
    }

    def genMod2(t: Tree, x: Any) = {
      nNames = 0
      val p = fromScala(t)
      println(pretty(p))
      val p1 = typeCheck(p,Nil)
      println(pretty(p1))

      {nNames = 0
      val ys = trans0(p1)(Map())
      val y = fromScala(ys)
      println(" "+pretty(y))
      val z = evalStd(y) { x => x}
      println(" "+z)
      assert(x == z)}

      {nNames = 0
      val y = transTrivial(p1)(Map())
      println(" "+pretty(y))
      val z = evalStd(y) { x => x}
      println(" "+z)
      assert(x == z)}

      {nNames = 0
      val y = transFullEta(p1)(Map())
      println(" "+pretty(y))
      val z = evalStd(y) { x => x}
      println(" "+z)
      assert(x == z)}
    }




    println("--- std ---")

    runStd(q"reset(shift(k => 1))", 1)
    runStd(q"reset(shift(k => k(1)))", 1)
    runStd(q"reset(shift(k => k(k(1))))", 1)
    runStd(q"reset(shift(k => k(k(k(1)))))", 1)

    runStd(q"reset(2 * shift(k => 1))", 1)
    runStd(q"reset(2 * shift(k => k(1)))", 2)
    runStd(q"reset(2 * shift(k => k(k(1))))", 4)
    runStd(q"reset(2 * shift(k => k(k(k(1)))))", 8)

    println("--- std gen ---")

    // reset(shift({ k: ? => 1}))
    // (x1 => k1 => k1(1))(x => k1 => k1(x))(x => x)
    // (k1 => k1(1))(x => x)
    // (x => x)(1)
    // 1

    // reset(shift({ k: ? => k(1)}))
    // (x1 => k1 => x1(1)((z => k1(z))))(x => k1 => k1(x))(x => x)
    // (k1 => (x => k2 => k2(x))(1)((z => k1(z))))(x => x)
    // (k1 => (k2 => k2(1))((z => k1(z))))(x => x)
    // (k1 => k1(1))(x => x)
    // (x => x)(1)
    // 1

    // reset((2 * shift({ k: ? => k(1)}))
    // (x1 => k1 => x1(1)((z => k1(z)))) (x => k1 => k1(2 * x)) (x => x)
    // (k1 => (x => k2 => k2(2 * x))(1) ((z => k1(z)))) (x => x)
    // (k1 => (k2 => k2(2 * 1)) ((z => k1(z)))) (x => x)
    // (k1 => ((z => k1(z)))(2 * 1)) (x => x)
    // (k1 => ((k1((2 * 1))))) (x => x)
    // ((((x => x)((2 * 1))))) 
    // ((((x => x)((2 * 1))))) 
    // 2*1

    genStd(q"(x => x)(1)", 1)
    genStd(q"reset(2)", 2)
    genStd(q"reset(shift(k => k(2)))", 2)


    genStd(q"reset(shift(k => 1))", 1)
    genStd(q"reset(shift(k => k(1)))", 1)
    genStd(q"reset(shift(k => k(k(1))))", 1)
    genStd(q"reset(shift(k => k(k(k(1)))))", 1)

    genStd(q"reset(2 * shift(k => 1))", 1)
    genStd(q"reset(2 * shift(k => k(1)))", 2)
    genStd(q"reset(2 * shift(k => k(k(1))))", 4)
    genStd(q"reset(2 * shift(k => k(k(k(1)))))", 8)

    println("--- mod ---")

    runMod(q"exit(reset(2 * shift(k => 1)))", 1)
    runMod(q"exit(reset(2 * shift(k => k(1))))", 2)
    runMod(q"exit(reset(2 * shift(k => k(k(1)))))", 4)
    runMod(q"exit(reset(2 * shift(k => k(k(k(1))))))", 8)

    runMod(q"exit(1 + shift(k => exit(5)))", 5)
    runMod(q"exit(1 + shift(k => k(1)))", 2)

    runMod(q"exit(reset(1 + reset(2 * shift(k1 => shift(k0 => k0(k1(1)))))))", 3)

    println("--- mod gen ---")

    genMod(q"exit((x => x)(1))", 1)
    genMod(q"exit(reset(2))", 2)
    genMod(q"exit(reset(shift(k => k(2))))", 2)

    genMod(q"exit(reset(2 * shift(k => 1)))", 1)
    genMod(q"exit(reset(2 * shift(k => k(1))))", 2)
    genMod(q"exit(reset(2 * shift(k => k(k(1)))))", 4)
    genMod(q"exit(reset(2 * shift(k => k(k(k(1))))))", 8)

    genMod(q"exit(1 + shift(k => exit(5)))", 5)
    genMod(q"exit(1 + shift(k => k(1)))", 2)

    genMod(q"exit(reset(1 + reset(2 * shift(k1 => shift(k0 => k0(k1(1)))))))", 3)

    // example: shift inside a lambda
    genMod(q"exit(reset(1 + reset(2 * (x => shift(k1 => shift(k0 => k0(k1(x)))))(1))))", 3)


    println("--- mod2 gen ---")

    genMod2(q"exit(((x:Nat) => x)(1))", 1)
    genMod2(q"exit(reset(2))", 2)
    genMod2(q"exit(reset(shift(k => k(2))))", 2)

    genMod2(q"exit(reset(2 * shift(k => 1)))", 1)
    genMod2(q"exit(reset(2 * shift(k => k(1))))", 2)
    genMod2(q"exit(reset(2 * shift(k => k(k(1)))))", 4)
    genMod2(q"exit(reset(2 * shift(k => k(k(k(1))))))", 8)

    genMod2(q"exit(1 + shift(k => exit(5)))", 5)
    genMod2(q"exit(1 + shift(k => k(1)))", 2)

    // this does not type check!!!
    // genMod2(q"exit(reset(1 + reset(2 * shift(k1 => shift(k0 => k0(k1(1)))))))", 3)
    genMod2(q"exit(reset(1 + reset(2 * shift(k1 => k1(shift(k0 => k0(1)))))))", 3)

    // this does not type check!!!
    // genMod2(q"exit(reset(1 + reset(2 * (x => shift(k1 => shift(k0 => k0(k1(x)))))(1))))", 3)
    genMod2(q"exit(reset(1 + reset(2 * ((x:Nat) => shift(k1 => k1(shift(k0 => k0(x)))))(1))))", 3)



    // TODO:
    // + codegen
    // + typing
    // - tupled instead of curried args

    println("DONE")
  }
}