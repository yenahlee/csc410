include "LTL.dfy"

type PropValuation = Formula -> bool

// evaluate formula using propositional logic
// used to determine if a formula is a propositional tautology
ghost function PropEval(
  f: Formula,
  v: PropValuation
): bool
  decreases f
{
  match f
  case Not(p) => !PropEval(p, v)
  case And(p, q) =>
    PropEval(p, v) && PropEval(q, v)
  case Imp(p, q) =>
    PropEval(p, v) ==> PropEval(q, v)
  case Iff(p, q) =>
    PropEval(p, v) == PropEval(q, v)
  case _ => v(f)
}

// formula is propositional tautology if it evaluates to true under all propositional valuations
ghost predicate PropTautology(f: Formula)
{
  forall v: PropValuation :: PropEval(f, v)
}

// create a propositional valuation from a trace and time
ghost function SemanticValuation(
  m: Trace,
  t: nat
): PropValuation
{
  (f: Formula) => Sat(f, m, t)
}

// helper: show that propositional evaluation matches satisfaction in a trace
lemma PropEvalMatchesSat(
  f: Formula,
  m: Trace,
  t: nat
)
  ensures
    PropEval(f, SemanticValuation(m, t))
    == Sat(f, m, t)
  decreases f
{
  match f
  case Not(p) =>
    PropEvalMatchesSat(p, m, t);

  case And(p, q) =>
    PropEvalMatchesSat(p, m, t);
    PropEvalMatchesSat(q, m, t);

  case Imp(p, q) =>
    PropEvalMatchesSat(p, m, t);
    PropEvalMatchesSat(q, m, t);

  case Iff(p, q) =>
    PropEvalMatchesSat(p, m, t);
    PropEvalMatchesSat(q, m, t);

  case _ =>
    assert SemanticValuation(m, t)(f)
      == Sat(f, m, t);
}

// R1: if w is a propositional tautology, then ⊢ w

lemma R1Sound(f: Formula)
  requires PropTautology(f)
  ensures Valid(f)
{
  forall m: Trace, t: nat
    ensures Sat(f, m, t)
  {
    PropEvalMatchesSat(f, m, t);

    assert PropEval(
      f, SemanticValuation(m, t)
    );

    assert Sat(f, m, t);
  }
}

// R2: if ⊢ w₁ ⊃ w₂ and ⊢ w₁, then ⊢ w₂

lemma R2Sound(p: Formula, q: Formula)
  requires Valid(p)
  requires Valid(Imp(p, q))
  ensures Valid(q)
{
  forall m: Trace, t: nat
    ensures Sat(q, m, t)
  {
    // p holds at this trace and time
    assert Sat(p, m, t);

    // p -> q also holds here
    assert Sat(Imp(p, q), m, t);

    // expand implication
    assert Sat(Imp(p, q), m, t) ==
      (Sat(p, m, t) ==> Sat(q, m, t));

    assert Sat(q, m, t);
  }
}

// R3: if ⊢ w, then ⊢ □w

lemma R3Sound(p: Formula)
  requires Valid(p)
  ensures Valid(Always(p))
{
  forall m: Trace, t: nat
    ensures Sat(Always(p), m, t)
  {
    // show p holds at every future time
    forall k: nat | t <= k
      ensures Sat(p, m, k)
    {
      // valid(p) means p holds at every time
      assert Sat(p, m, k);
    }
    // so always(p) holds at time t
    assert Sat(Always(p), m, t);
  }
}

