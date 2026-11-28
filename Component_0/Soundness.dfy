
include "Axioms.dfy"
include "Rules.dfy"

// a derivation is a finite proof tree
// each constructor represents an axiom or rule

datatype Derivation =
  | Ax1(p: Formula)
  | Ax2(p: Formula, q: Formula)
  | Ax3(p: Formula)
  | Ax4(p: Formula, q: Formula)
  | Ax5(p: Formula)
  | Ax6(p: Formula)
  | Ax7(p: Formula, q: Formula)
  | Ax8(p: Formula, q: Formula)
  | PropRule(f: Formula)
  | ModusPonens(
      left: Derivation,
      right: Derivation
    )
  | NecRule(d: Derivation)


// return the formula proved by a derivation

ghost function Conclusion(d: Derivation): Formula
  decreases d
{
  match d
  case Ax1(p) =>
    Iff(Eventually(p), Not(Always(Not(p))))

  case Ax2(p, q) =>
    Imp(
      Always(Imp(p, q)),
      Imp(Always(p), Always(q))
    )

  case Ax3(p) =>
    Iff(Next(Not(p)), Not(Next(p)))

  case Ax4(p, q) =>
    Imp(
      Next(Imp(p, q)),
      Imp(Next(p), Next(q))
    )

  case Ax5(p) =>
    Imp(
      Always(p),
      And(p, And(Next(p), Next(Always(p))))
    )

  case Ax6(p) =>
    Imp(
      Always(Imp(p, Next(p))),
      Imp(p, Always(p))
    )

  case Ax7(p, q) =>
    Imp(Always(p), Until(p, q))

  case Ax8(p, q) =>
    Iff(
      Until(p, q),
      Imp(
        Not(q),
        And(p, Next(Until(p, q)))
      )
    )

  case PropRule(f) => f

// the fallback handles malformed derivations
// WellFormed guarantees that valid MP steps always use the Imp(p, q) branch
  case ModusPonens(left, right) =>
    match Conclusion(right) {
        case Imp(p, q) => q
        case _ => Conclusion(left)
    }

  case NecRule(d0) =>
    Always(Conclusion(d0))
}

// check that every step follows a valid rule
ghost predicate WellFormed(d: Derivation)
  decreases d
{
  match d
  case Ax1(p) => true
  case Ax2(p, q) => true
  case Ax3(p) => true
  case Ax4(p, q) => true
  case Ax5(p) => true
  case Ax6(p) => true
  case Ax7(p, q) => true
  case Ax8(p, q) => true

  case PropRule(f) =>
    PropTautology(f)

  case ModusPonens(left, right) =>
    WellFormed(left) &&
    WellFormed(right) &&
    (exists q: Formula ::
      Conclusion(right) ==
        Imp(Conclusion(left), q))

  case NecRule(d0) =>
    WellFormed(d0)
}

// overall soundness theorem:
// every well-formed derivation proves a valid formula.
lemma Soundness(d: Derivation)
  requires WellFormed(d)
  ensures Valid(Conclusion(d))
  decreases d
{
  match d
  case Ax1(p) =>
    A1Sound(p);

  case Ax2(p, q) =>
    A2Sound(p, q);

  case Ax3(p) =>
    A3Sound(p);

  case Ax4(p, q) =>
    A4Sound(p, q);

  case Ax5(p) =>
    A5Sound(p);

  case Ax6(p) =>
    A6Sound(p);

  case Ax7(p, q) =>
    A7Sound(p, q);

  case Ax8(p, q) =>
    A8Sound(p, q);

  case PropRule(f) =>
    R1Sound(f);

  case ModusPonens(left, right) =>
    // inductive hypothesis:
    // both smaller derivations are sound
    Soundness(left);
    Soundness(right);
    
    assert exists q: Formula ::
      Conclusion(right) ==
        Imp(Conclusion(left), q);

    ghost var q: Formula :|
      Conclusion(right) ==
        Imp(Conclusion(left), q);

    assert Valid(Conclusion(left));
    assert Valid(Imp(Conclusion(left), q));

    R2Sound(Conclusion(left), q);

    assert Valid(q);
    assert Conclusion(d) == q;

  case NecRule(d0) =>
    // inductive hypothesis
    Soundness(d0);

    // apply R3
    R3Sound(Conclusion(d0));
}
