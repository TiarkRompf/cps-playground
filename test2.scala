package test2

// test cases for 0 or 1 return types (undelimited continuations)

/*
TODO: 
  + parsing: how to distinguish 1st/2nd? (default: all 2nd)
  + proper 1st/2nd type checking
  + type-preserving cps
  + 1st/2nd class for tuple fields
  + type check terms again after cps
  - cps transform: cps arg 1st/2nd based on context (see also typing for Shift) -- do test cases first?
*/

object Test {

  // --------------- terms and types ---------------

  abstract class Term {
    var tpe: EType = _
    def withType(ty: EType): this.type = { tpe = ty; this }
  }

  case class Const(x: Any) extends Term
  case class Var(x: String, n:Int) extends Term {
    var def_index: Int = -1
    var use_index: Int = -1
  }
  case class Lam(x: String, n: Int, t: Type, y: Term) extends Term
  case class App(f: Term, x: Term) extends Term
  case class Let(x: String, n: Int, t: Type, y: Term, z: Term) extends Term
  case class If(c: Term, a: Term, b: Term) extends Term
  case class Plus(x: Term, y: Term) extends Term
  case class Times(x: Term, y: Term) extends Term

  case class Shift(x: Term) extends Term
  case class Exit(x: Term) extends Term

  case class ILam(n: Int, t: Type, f: Term => Term) extends Term // "administrative" lambda, should inline

  case class Tuple(xs: List[Term]) extends Term
  case class Field(x: Term, y: Int) extends Term

  case class RefTuple(n: Int, xs: List[Term]) extends Term // a by-reference tuple, allocated on the stack or heap (used for closures)
  case class RefField(x: Term, y: Int) extends Term


  abstract class Type
  case object Unknown extends Type
  case object Unit extends Type
  case object Nat extends Type
  case object Bool extends Type
  case class Fun(x: Type, n: Int, y: EType) extends Type
  case class Product(xs: List[(Int,Type)]) extends Type

  type EType = Option[Type] // None = doesn't return
  val Void = None

  // Note on usage of 'n': 
  // 1 means first class
  // 2 means second class
  // 0 means unknown (e.g. in typeConforms)

  // --------------- type checking ---------------

  def sanitize(env: Map[String,(Int,Type)], m: Int) = env filter (_._2._1 <= m)

  def typeCheck1(t: Term, m: Int, ty: EType)(implicit env: Map[String,(Int,Type)]): Term = t match {
    case Const(x: Int) =>       t withType Some(Nat)
    case Const(x: Boolean) =>   t withType Some(Bool)
    case Var(x,n) =>            val (n1,tpe) = sanitize(env,m)(x); assert(n == 0 || n == n1); Var(x,n1) withType Some(tpe)

    case Exit(x) =>
      val x1 = typeCheck(x, 1, Some(Nat))
      Exit(x1) withType Void

    case Plus(a, b) =>
      val a1 = typeCheck(a, 2, Some(Nat))
      val b1 = typeCheck(b, 2, Some(Nat))
      Plus(a1, b1) withType Some(Nat)

    case Times(a, b) =>
      val a1 = typeCheck(a, 2, Some(Nat))
      val b1 = typeCheck(b, 2, Some(Nat))
      Times(a1, b1) withType Some(Nat)

    case Tuple(as) =>
      val Some(Product(ats)) = ty //
      val as1 = (as zip ats) map { case (a, (n, t)) => assert(n == m) /* relax? */; typeCheck(a, m, Some(t)) } 
      Tuple(as1) withType Some(Product(as1 map (a => (m,a.tpe.get))))

    case Field(a, n) =>
      val a1 = typeCheck(a, 2, Some(Unknown)) // expected type? we don't know size of tuple ...
      val Some(Product(as)) = a1.tpe
      assert(m <= as(n)._1)
      Field(a1, n) withType Some(as(n)._2)

    case Let(x,n,t,y,z) =>
      val y1 = typeCheck(y, n, Some(t))(env + (x -> (n,t)))
      val z1 = typeCheck(z, m, ty)(env + (x -> (n,y1.tpe.get)))
      Let(x,n,t,y1,z1) withType z1.tpe

    case If(c,a,b) =>
      val c1 = typeCheck(c, 2, Some(Nat))
      val a1 = typeCheck(a, m, ty)
      val b1 = typeCheck(b, m, ty)
      assert(a1.tpe == b1.tpe)
      If(c1,a1,b1) withType a1.tpe

    case App(f, x) => 
      val f1 = typeCheck(f, 2, Some(Fun(Unknown,0,ty)))
      val Some(Fun(ty1,n,ty2)) = f1.tpe
      val x1 = typeCheck(x, n, Some(ty1))
      App(f1,x1) withType ty2

    case Lam(x, n0, t0, y) => 
      ty match {
        case Some(Fun(te, ne, ts2)) =>
          val n1 = if (n0 == 0) ne else n0
          val t1 = if (t0 == Unknown) te else t0
          assert(n1 != 0)
          assert(t1 != Unknown,
            s"missing parameter type!\n" +
            s"    expression: "+pretty(t) + "\n" +
            s"    expected:   "+ty.map(pretty).mkString(" / ")
          )
          val y1 = typeCheck(y, 1, ts2)(sanitize(env,m) + (x -> (n1,t1)))
          Lam(x, n1, t1, y1) withType Some(Fun(t1, n1, y1.tpe))
        //case _ => // error
      }

    case Shift(f) =>
      val Some(t1) = ty
      val f1 = typeCheck(f, 2, Some(Fun(Fun(t1,1,Void),2,Void))) // NOTE: replacing 1 with m would be more precise (but then we should perform CPS with m from context, too, which we may need anyways)
      val Some(Fun(Fun(t2,1,ts2),1,ts3)) = f1.tpe
      assert(typeConformsE(ts2,ts3))
      Shift(f1) withType Some(t2)
  }

  def typeCheck(t: Term, m: Int, ty: EType)(implicit env: Map[String,(Int,Type)]): Term = {
    // if (t.tpe ne null) return t

    // def assert(b: Boolean, s: String) = if (!b) println(s) // continue on error
    def tce(t1: EType, t2: EType) = assert(typeConformsE(t1, t2),
        s"type error!\n" +
        s"    expression: "+pretty(t) + "\n" +
        s"    expected:   "+t2.map(pretty).mkString(" / ") + "\n" +
        s"    actual:     "+t1.map(pretty).mkString(" / ")
      )

    if (t.tpe ne null) tce(t.tpe, ty) // previous assigned type must match expected

    var t1 = typeCheck1(t,m,ty)
    tce(t1.tpe, ty) // computed type must match expected

    if (t.tpe ne null) tce(t.tpe, t1.tpe) // previous assigned type must match computed type

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
    case (Product(ts1), Unknown) => ts1 forall { case (n1,t1) => typeConforms(t1, Unknown) && n1 != 0 }
    case (Product(ts1), Product(ts2)) => ts1.length == ts2.length && (ts1 zip ts2).forall { case ((n1,t1),(n2,t2)) => typeConforms(t1,t2) && n1 != 0 && (n2 == 0 || n1 == n2) }
    case _ => false
  }


  // --------------- parsing (from Scala quasiquotes) ---------------

  import scala.reflect.runtime.universe.{Type => SType, _}
  def fromScala(t: Tree): Term = t match {
    case Literal(Constant(x))    => Const(x)
    case Ident(x)                => Var(x.toString,0)
    case q"exit($x)"             => Exit(fromScala(x))
    case q"shift($x)"            => Shift(fromScala(x))
    case q"($x:${t}) => $y"      => Lam(x.toString,fromScalaN(t),fromScalaT(t),fromScala(y))
    case q"$x + $y"              => Plus(fromScala(x),fromScala(y))
    case q"$x - $y"              => Plus(fromScala(x),Times(Const(-1),fromScala(y)))
    case q"$x * $y"              => Times(fromScala(x),fromScala(y))
    case q"val $x:${t} = $y; $z" => Let(x.toString,fromScalaN(t),fromScalaT(t),fromScala(y),fromScala(z))
    case q"if($c) $a else $b"    => If(fromScala(c),fromScala(a),fromScala(b))
    case Apply(f,x::Nil)         => App(fromScala(f),fromScala(x))
  }

  def fromScalaT(t: Tree): Type = t match {
    case tq"$a @fst"  => fromScalaT(a)
    case tq"$a @snd"  => fromScalaT(a)
    case tq"Int"      => Nat
    case tq"Nat"      => Nat
    case tq"$a => $b" => Fun(fromScalaT(a), fromScalaN(a), Some(fromScalaT(b)))
    case _ if t.toString == "Any"      => Unknown
    case _ if t.toString == "<type ?>" => Unknown
  }

  def fromScalaN(t: Tree): Int = t match {
    case tq"$a @fst" => 1
    case tq"$a @snd" => 2
    case tq"$a"      => 2  // default: 2nd class
  }

  // --------------- pretty printing ---------------

  def pretty(t: Term): String = t match {
    case Const(x)       => x.toString
    case t@Var(x,n)     if t.def_index >= 0 => x.toString + "$" + (t.use_index - t.def_index)
    case Var(x,n)       => x.toString
    case App(f,x)       => s"${pretty(f)}(${prettyb(x)})"
    case Lam(x,n,t,y)   if t == Unknown => s"($x $n=> ${prettyb(y)})"
    case Lam(x,n,t,y)   => s"($x: ${prettyb(t)} $n=> ${prettyb(y)})"
    case Plus(x,y)      => s"(${pretty(x)} + ${pretty(y)})"
    case Times(x,y)     => s"(${pretty(x)} * ${pretty(y)})"
    case Exit(x)        => s"exit(${prettyb(x)})"
    case Shift(x)       => s"shift(${prettyb(x)})"
    case ILam(n,t,f)    => s"(.. => ..)"
    case Tuple(xs)      => xs map pretty mkString ","
    case Field(x,n)     => s"${pretty(x)}.$n"
    case RefTuple(n,xs) => s"[#$n "+ (xs map pretty mkString ",") + "]"
    case RefField(x,n)  => s"${pretty(x)}.$n"
    case Let(x,n,t,y,z) if t == Unknown => s"val $x $n= ${pretty(y)}\n${pretty(z)}"
    case Let(x,n,t,y,z) => s"val $x: ${prettyb(t)} $n= ${pretty(y)}\n${pretty(z)}"
    case If(c,a,b)      => s"if (${pretty(c)}) ${pretty(a)} else ${pretty(b)}"
  }

  def prettyb(t: Term): String = t match {
    case Lam(x,n,t,y) if t == Unknown => s"$x $n=> ${prettyb(y)}"
    case Lam(x,n,t,y) => s"$x: ${prettyb(t)} $n=> ${prettyb(y)}"
    case Plus(x,y)    => s"${pretty(x)} + ${pretty(y)}"
    case Times(x,y)   => s"${pretty(x)} * ${pretty(y)}"
    case _            => pretty(t)
  }


  def pretty(t: EType): String = t map pretty mkString " / "

  def pretty(t: Type): String = t match {
    case Unknown     => "?"
    case Fun(a,n,b)  => s"${prettyb(a)} $n=> ${pretty(b)}"
    case Product(as) => as.map({ case (n,t) => prettyb(t)+"^"+n}).mkString(" * ")
    case _           => t.toString
  }

  def prettyb(t: Type): String = t match {
    case Fun(a,n,b)  => s"(${prettyb(a)} $n=> ${pretty(b)})"
    case Product(as) => s"(${ as.map({ case (n,t) => prettyb(t)+"^"+n}).mkString(" * ") })"
    case _           => pretty(t)
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

    case RefTuple(n,xs) =>      evalStd(Tuple(xs))(k)
    case RefField(x,n) =>       evalStd(Field(x,n))(k)


    case Lam(x,n,t,y) =>        k((x1:Any) => (k1:Any => Any) => evalStd(y)(k1)(env + (x -> x1)))

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
        f1((x:Any) => (k1:Any => Any) => k1(k(x)))(x => x)
      }

    // case Reset(x) => 
    //  k(evalStd(x)(x => x))

    case Exit(x) => evalStd(x) { u => u }


  } catch { case e => (println("error: "+pretty(t)+"    "+e)); throw e }

  
  // --------------- transform utils ---------------

  var nNames = 0
  def freshv(s: String, n: Int) = try Var(s+nNames,n) finally nNames += 1

  def app(x: Term, y: Term) = x match {
    case ILam(n, tpe, f) => 
      assert(y.tpe.get == tpe, s"${y.tpe.get} != $tpe")
      f(y)
    case _ => 
      val Some(Fun(a,n,b)) = x.tpe
      val y1 = proper(y)
      assert(y1.tpe.get == a, s"${y1.tpe.get} != $a for term ${pretty(x)}(${pretty(y1)})")
      App(x,y1) withType b
  }

  def proper(f: Term): Term = f match {
    case ILam(n, tpe, f) => fun(tpe, n)(f)
    case Tuple(xs) => Tuple(xs map proper) withType f.tpe
    case _ => f
  }

  def ifun(tpe: Type, n: Int = 1)(f: Term => Term): Term = ILam(n, tpe, f) withType Some(Fun(tpe,n,Void)) // default: mark autogenerated functions (n = 1) --> assume their args do escape

  def field(x: Term, n: Int): Term = x match {
    case Tuple(xs) => xs(n)
    case _ => Field(x,n) withType Some(x.tpe.get.asInstanceOf[Product].xs(n)._2)
  }

  def explode(f: (Term, Term) => Term)(x: Term): Term = f(field(x,0),field(x,1))
  def explode(f: (Term, Term, Term) => Term)(x: Term): Term = f(field(x,0),field(x,1),field(x,2))
  def explode(f: (Term, Term, Term, Term) => Term)(x: Term): Term = f(field(x,0),field(x,1),field(x,2),field(x,3))

  def fun(tpe: Type, n: Int = 2)(f: Term => Term): Term = {
      val z = freshv("z",n) // default: mark proper functions (n = 2) --> assume their args don't escape
      val y = proper(f(z withType Some(tpe) ))
      Lam(z.x, n, tpe, y) withType Some(Fun(tpe,n,y.tpe))
  }


  // def ifun(t1: Type, t2: Type)(f: (Term, Term) => Term): Term = ifun(Product(List(t1,t2)))(explode(f)_)
  // def ifun(t1: Type, t2: Type, t3: Type)(f: (Term, Term, Term) => Term): Term = ifun(Product(List(t1,t2,t3)))(explode(f)_)


  def fun(t1: Type, n1: Int, t2: Type, n2: Int)(f: (Term, Term) => Term): Term = fun(Product(List((n1,t1),(n2,t2))),2)(explode(f)_)  // XXX tuple 1st/2nd? right now we're discarding n1 (ok if it's a closure) ...
  // def fun(t1: Type, t2: Type, t3: Type)(f: (Term, Term, Term) => Term): Term = fun(Product(List(t1,t2,t3)))(explode(f)_)
  // def fun(t1: Type, t2: Type, t3: Type, t4: Type)(f: (Term, Term, Term, Term) => Term): Term = fun(Product(List(t1,t2,t3,t4)))(explode(f)_)

  def app(f: Term, x: Term, y: Term): Term = {
    val Some(Fun(Product(List((n1,a1),(n2,a2))),_,_)) = f.tpe
    app(f, Tuple(List(x,y)) withType Some(Product(List((n1,x.tpe.get), (n2,y.tpe.get)))))
  }
  // def app(f: Term, x: Term, y: Term, z: Term): Term = app(f, Tuple(List(x,y,z)) withType Some(Product(List(x.tpe.get, y.tpe.get, z.tpe.get))))
  // def app(f: Term, x: Term, y: Term, z: Term, u: Term): Term = app(f, Tuple(List(x,y,z,u)) withType Some(Product(List(x.tpe.get, y.tpe.get, z.tpe.get, y.tpe.get))))

  def setN(f: Term, n: Int) = f match {
    case Lam(x,n0,t,y) => assert(n0 == n); f// Lam(x,n,t,y)
    case _ => f
  }

  // --------------- selective cps transform ---------------

  def transType(t: EType): EType = t match {
    case None => None
    case Some(t) => Some(Fun(cpsType(t),1,Void))
  }
  def transType(t: Type): Type = t match {
    case Nat => Nat
    case Bool => Bool
    case Fun(a,n,None) => Fun(transType(a),n,None)
    case Fun(a,n,Some(b)) => Fun(Product(List((n,transType(a)),(2,cpsType(b)))),2,Void)
    case Product(xs) => Product(xs map { case (n,t) => (n,transType(t)) })
  }

  def cpsType(t: Type) = Fun(transType(t),1,Void)


  def transCPS(t: Term)(env: Map[String,Term]): Term = {
    val t1 = transCPS1(t)(env)
    assert(t1.tpe == transType(t.tpe), s"${t1.tpe} != ${transType(t.tpe)}\n for term [[ $t ]] = $t1")
    t1
  }


  def transCPS1(t: Term)(env: Map[String,Term]): Term = t match {
    case Const(x: Int) =>       ifun(cpsType(Nat))(k => app(k, (Const(x) withType Some(Nat))))
    case Const(x: Boolean) =>   ifun(cpsType(Nat))(k => app(k, (Const(x) withType Some(Bool))))
    case Plus(x,y) =>           ifun(cpsType(Nat))(k => app(transCPS(x)(env), ifun(Nat) { u => app(transCPS(y)(env), ifun(Nat) { v => app(k, Plus(u,v) withType Some(Nat)) })}))
    case Times(x,y) =>          ifun(cpsType(Nat))(k => app(transCPS(x)(env), ifun(Nat) { u => app(transCPS(y)(env), ifun(Nat) { v => app(k, Times(u,v) withType Some(Nat)) })}))
    case Var(x,n) =>            ifun(cpsType(t.tpe.get))(k => app(k, (env(x))))

    case Exit(x) =>             app(transCPS(x)(env), ifun(transType(x.tpe.get))(x => Exit(x) withType Void))

    case Lam(x,n,tp,y) =>
      val Some(Fun(t1,n1,ts2)) = t.tpe; assert(tp == t1 && n == n1)
      if (ts2 == Void)
        ifun(cpsType(t.tpe.get))(k => app(k, fun(transType(tp),n)(x1 => transCPS(y)(env + (x -> x1))))) // do not cps transform!
      else 
        ifun(cpsType(t.tpe.get))(k => app(k, fun(transType(tp),n,cpsType(ts2.get),2)((x1,k1) => app(transCPS(y)(env + (x -> x1)), k1))))

    case App(x,y) =>
      if (t.tpe == Void)
        app(transCPS(x)(env), ifun(transType(x.tpe.get)) { u => app(transCPS(y)(env), ifun(y.tpe.get) { v => app(u,v) })})
      else
        ifun(cpsType(t.tpe.get))(k => app(transCPS(x)(env), ifun(transType(x.tpe.get)) { u => app(transCPS(y)(env), ifun(transType(y.tpe.get)) { v => app(u,v,k) })}))

    case Let(x,n,tp, y: Lam, z) =>
      if (t.tpe == Void)
        Let(x,n,transType(tp),
          app(transCPS(y)(env + (x -> (Var(x,n) withType Some(transType(tp))))), ifun(transType(y.tpe.get)) { u => u }), // id cont, we know it's a value
          transCPS(z)(env + (x -> (Var(x,n) withType Some(transType(tp))))) ) withType Void
      else
        ifun(cpsType(t.tpe.get))(k => 
          Let(x,n,transType(tp), 
            app(transCPS(y)(env + (x -> Var(x,n))), ifun(transType(y.tpe.get)) { u => u }), // id cont, we know it's a value
            app(transCPS(z)(env + (x -> Var(x,n))), k) ) withType Void)

    case If(c,a,b) =>
      if (t.tpe == Void) 
        app(transCPS(c)(env), ifun(transType(c.tpe.get)) { c2 =>
          val ift = fun(Product(Nil),1)(x => transCPS(a)(env))
          val iff = fun(Product(Nil),1)(x => transCPS(b)(env))
          app(If(c2, ift, iff) withType ift.tpe, Tuple(Nil) withType Some(Product(Nil))) }) withType Void
      else
        ifun(cpsType(t.tpe.get)) { k0 =>
          app(transCPS(c)(env), ifun(transType(c.tpe.get)) { c2 =>
            val k = proper(k0) // XXX TODO: let bind?
            val ift = fun(Product(Nil),1)(x => app(transCPS(a)(env),k))
            val iff = fun(Product(Nil),1)(x => app(transCPS(b)(env),k))
            app(If(c2, ift, iff) withType ift.tpe, Tuple(Nil) withType Some(Product(Nil))) })
        }

    case Shift(f) =>
      ifun(cpsType(t.tpe.get))(k => 
        app(transCPS(f)(env), ifun(f.tpe.get) { f1 => 
          app(f1, k)
      }))

  }


  // --------------- variable transform (assign numeric indexes -- not strictly needed) ---------------

  def transVars(t: Term)(implicit env: (List[String],List[String])): Term = {
    transVars1(t) withType t.tpe
  }

  def transVars1(t: Term)(implicit env: (List[String],List[String])): Term = t match {
    case Const(x) =>       t
    case Plus(x,y) =>      Plus(transVars(x), transVars(y))
    case Times(x,y) =>     Times(transVars(x), transVars(y))
    case Var(x,n) =>       val e = n match { case 1 => env._1 case 2 => env._2 }; val t1 = Var(x,n); t1.use_index = e.length; t1.def_index = e.lastIndexOf(x); t1

    case Exit(x) =>        Exit(transVars(x))

    case Tuple(xs) =>      Tuple(xs map transVars)
    case Field(x,n) =>     Field(transVars(x), n)

    case Lam(x,n,tp,y) =>
      n match {
        case 1 => Lam(x, n, tp, transVars(y)(env._1 :+ x, env._2))
        case 2 => Lam(x, n, tp, transVars(y)(env._1, env._2 :+ x))
      }

    case App(x,y) =>       App(transVars(x), transVars(y))

    case Let(x,n,tp, y: Lam, z) =>
      n match {
        case 1 => Let(x, n, tp, transVars(y)(env._1 :+ x, env._2), transVars(z)(env._1 :+ x, env._2))
        case 2 => Let(x, n, tp, transVars(y)(env._1, env._2 :+ x), transVars(z)(env._1, env._2 :+ x))
      }

    case If(c,a,b) =>      If(transVars(c), transVars(a), transVars(b))
  }


  // --------------- closure conversion ---------------

  // Note: terms remain typed throughout closure conversion, but types do not change. 
  // So afterwards, function types can refer to both closures and raw functions (should this be changed?)

  def freeVars(t: Term): Set[String] = t match {
    case Const(x)        => Set()
    case Plus(x,y)       => freeVars(x) ++ freeVars(y)
    case Times(x,y)      => freeVars(x) ++ freeVars(y)
    case Var(x,n)        => Set(x)
    case Field(x,n)      => freeVars(x)
    case Tuple(Nil)      => Set()
    case Tuple(xs)       => (xs map freeVars).reduce(_ ++ _)
    case Exit(x)         => freeVars(x)
    case If(c,a,b)       => freeVars(c) ++ freeVars(a) ++ freeVars(b)
    case Let(x,n,tp,y,z) => (freeVars(y) ++ freeVars(z)) - x
    case Lam(x,n,tp,y)   => freeVars(y) - x
    case App(x,y)        => freeVars(x) ++ freeVars(y)
  }

  def istrivial(x: Term): Boolean = x match {
    case Var(x,n)        => true
    case Field(x,n)      => istrivial(x)
    case Tuple(xs)       => xs forall istrivial
    case _ => false
  }

  def transClos(t: Term, m: Int)(implicit env: Map[String,(Int,Term)]): Term = {
    transClos1(t, m) withType t.tpe
  }
  def transClos1(t: Term, m: Int)(implicit env: Map[String,(Int,Term)]): Term = t match {
    case Const(x) =>       t
    case Plus(x,y) =>      Plus(transClos(x, 2), transClos(y, 2))
    case Times(x,y) =>     Times(transClos(x, 2), transClos(y, 2))
    case Var(x,n) =>       env(x)._2

    case Exit(x) =>        Exit(transClos(x, 1))

    case Tuple(xs) =>      Tuple(xs map (transClos(_, m))) // XXX type 1st/2nd?
    case Field(x,n) =>     Field(transClos(x, 2), n)

    case If(c,a,b) =>      If(transClos(c, 2), transClos(a, m), transClos(b, m))

    case Let(f,nf,tf,Lam(x,n,tp,y),z) =>
      val free = (freeVars(t) - f).toList
      def lookup(e1: Term): Map[String,(Int,Term)] = (for ((x,i) <- free.zipWithIndex) yield (x,(env(x)._1, RefField(e1,i+1)))).toMap
      val closureType = Product((nf,tf)::(free map env map (p => (p._1,p._2.tpe.get))))

      val ff = fun(closureType,nf,tp,n) { (e1,x1) => 
        transClos(y, 1)(env ++ lookup(e1) + (f -> (nf,e1)) + (x -> (n,x1))) }

      val cl = RefTuple(nf, ff::(free map env map (_._2))) withType Some(tf) // Note: will be assigned function type
      
      Let(f,nf,tf,cl,transClos(z, m)(env + (f -> (nf,cl))))

    case Lam(x,n,tp,y) =>
      val free = freeVars(t).toList
      def lookup(e1: Term): Map[String,(Int,Term)] = (for ((x,i) <- free.zipWithIndex) yield (x,(env(x)._1, RefField(e1,i+1)))).toMap
      val closureType = Product((2,t.tpe.get)::(free map env map (p => (p._1,p._2.tpe.get))))

      val f = fun(closureType,2,tp,n) { (e1,x1) => 
        transClos(y, 1)(env ++ lookup(e1) + (x -> (n,x1))) }

      RefTuple(m, f::(free map env map (_._2))) // Note: will be assigned function type

    case App(x,y) =>
      val u = transClos(x, 2)

      // proper type for x:
      //   was: A -> B
      //   now: F = (F x A -> B, E)
      // we do not have recursive types or existentials so we keep the original type ...

      val Some(Fun(a,n,b)) = u.tpe
      val closureType = Fun(a,n,b)
      val rawFuncType = Fun(Product(List((2,closureType),(n,a))),2,b) // note: we assume closure is 2nd class here, 
      // although some functions may leak it --- this is fine because it will have been known to be 1st class and 
      // therefore heap-allocated at the function creation site (it must have been demoted to 2nd class in present context)

      def extractRawFunc(u: Term) = RefField(u,0) withType Some(rawFuncType)

      val v = transClos(y, n)

      if (istrivial(u)) {
        app(extractRawFunc(u), u, v)
      } else {
        val u1 = (freshv("cl",2) withType u.tpe).asInstanceOf[Var]
        Let(u1.x,2,u.tpe.get,u,
          app(extractRawFunc(u1), u1, v))
      }
  }



  // --------------- low-level evaluator (explicit call stack) ---------------

  // Note: this was implemented before closure conversion, could go more low-level now

  def evalLLP(t: Term): Any = {
    var fs = Map[String,Any]()
    var mem = new Array[Any](1000)
    var fp = 100 // start of stack frame
    var ap = 100
    var sp = 101
    var hp = 500

    mem(99) = 1 // we use this as empty tuple (size 1 incl length)

    val exit = (x: Any) => return x

    case class Clos(f: Lam, sp1: Int)
    case class Addr(x: Int)

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

        {
          val Clos(l1@Lam(x,n,t,y), sp1) = f1
          // reset sp if arg escape (continuation call!) TODO: should decide based on type?
          // (escape behavior seems to indicate that the arg should live on the heap ... but this would
          // be expensive for continuations! we avoid this by more precise closure conversion. arguments
          // are always passed on the stack but copied into heap-allocated closures if necessary)
          val clos::args = f.tpe match { case Some(Fun(Product(xs),2,_)) => xs case Some(Fun(a,n,_)) => List((n,a)) }
          if (args.forall(_._1 == 1)) { // if all args (except closure) are 1st class, we can shrink stack
            val List(Addr(clos),arg) = x1
            assert(sp1 == clos) // TODO: we assume here that closure is stack allocated (2nd class!). may not be true ...
            val closSize = mem(clos).asInstanceOf[Int]
            println(s"*** JMP/RET reset sp $sp -> $clos+${closSize+1} ***")
            sp = clos + closSize + 1
          }
          mem(sp) = x1; sp += 1
          println(s"    mem(${sp-1}) = ${mem(sp-1)}")
          evalLLS(y)(Map(x -> (sp-1)))
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

      case Tuple(xs) =>
        xs.map(evalLLE)

      case Field(x,n) =>
        val xs = evalLLE(x).asInstanceOf[List[Any]]
        xs(n)

      case RefTuple(1, xs) => // heap
        val ys = xs.map(evalLLE)
        val a = hp
        mem(hp) = ys.length; hp += 1
        for (y <- ys) {
          mem(hp) = y; hp += 1
        }
        Addr(a)

      case RefTuple(2, xs) => // stack
        val ys = xs.map(evalLLE)
        val a = sp
        mem(sp) = ys.length; sp += 1
        for (y <- ys) {
          mem(sp) = y; sp += 1
        }
        Addr(a)

      case RefField(x,n) =>
        val Addr(a) = evalLLE(x)
        mem(a + 1 + n)

      case l@Lam(x,n,t,y) =>
        Clos(l,sp)
    }

    evalLLS(t)(Map())

  }



  def main(args: Array[String]): Unit = {

    def genMod3(t: Tree, x: Any) = {
      println("")

      println("-- parsing")
      nNames = 0
      val p = fromScala(t)
      println(pretty(p))

      println("-- type checking")
      nNames = 0
      val p1 = typeCheck(p,1,Void)(Map())
      println(pretty(p1))

      println("-- cps conversion")
      nNames = 0
      val y0 = transCPS(p1)(Map())
      val y1 = transVars(y0)(Nil,Nil)
      println(" "+pretty(y1))

      typeCheck(y1,1,Void)(Map()) // type check again!

      println("-- closure conversion")
      val y = transClos(y1,1)(Map())
      println(" "+pretty(y))

      //typeCheck(y,1,Void)(Map()) // closure conversion does not type check ...

      println("-- std eval")
      val u = evalStd(y)(x => x)(Map())
      println(" "+u)
      assert(x == u)

      println("-- low-level eval")
      val v = evalLLP(y)
      println(" "+v)
      assert(x == v)
    }



    println("--- mod2 gen ---")

    genMod3(q"exit(2)", 2)

    genMod3(q"exit(1+1)", 2)

    // genMod3(q"exit(((x:Nat) => x)(2))", 2) // TODO: don't consider primitive types as 1st/2nd class

    genMod3(q"exit(((x:Nat) => 2 * x)(1))", 2)

    // standard recursive functions, all 2nd class on the surface

    genMod3(q"val dec: (Nat => Nat) = n => if (n) dec(n-1) else 0; exit(dec(4))", 0)

    genMod3(q"val fac: (Nat => Nat) = n => if (n) n * fac(n-1) else 1; exit(fac(4))", 24)

    genMod3(q"val fib: (Nat => Nat) = n => if (n-1) fib(n-1)+fib(n-2) else 1; exit(fib(5))", 8)

    // some specific test cases:

    // 1. conditional in a 2nd class context should lead to (local) continuation with 2nd class argument
    genMod3(q"val x = if (1) ((x:Nat) => 1) else ((x:Nat) => 2); exit(0)", 0)

    // try the same with stack-allocated closures of different size
    genMod3(q"val a = 2; val x = if (1) ((x:Nat) => 1) else ((x:Nat) => a); exit(0)", 0)

    // 2. function call in a second class context -- test if this leads to 1st/2nd class confusion for continuation arg
    genMod3(q"val f = (y:Nat) => 1+y; val x = f(1); exit(0)", 0)

    // try again with 2nd class closure arg
    genMod3(q"val f = (y:Nat=>Nat) => y(1); val x = f(x=>1+x); exit(0)", 0)

    // 3. shift in second class context
    genMod3(q"val x: Nat = shift(k => k(1)); exit(1+x)", 2)


    println("DONE")
  }
}