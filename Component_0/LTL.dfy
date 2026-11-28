datatype Formula =
  | Atom(id: nat)
  | Not(p: Formula)
  | And(p: Formula, q: Formula)
  | Imp(p: Formula, q: Formula)
  | Iff(p: Formula, q: Formula)
  | Next(p: Formula)
  | Always(p: Formula)
  | Eventually(p: Formula)
  | Until(p: Formula, q: Formula)

// (t, id) -> true if proposition id is true at time t
type Trace = (nat, nat) -> bool

// return true if formula f is satisfied at time t in trace m
ghost function Sat(f: Formula, m: Trace, t: nat): bool
  decreases f
{
  match f
  case Atom(id) =>
    m(t, id)

  case Not(p) =>
    !Sat(p, m, t)

  case And(p, q) =>
    Sat(p, m, t) && Sat(q, m, t)

  case Imp(p, q) =>
    Sat(p, m, t) ==> Sat(q, m, t)

  case Iff(p, q) =>
    Sat(p, m, t) == Sat(q, m, t)

  case Next(p) =>
    Sat(p, m, t + 1)

  case Always(p) =>
    forall k: nat ::
      t <= k ==> Sat(p, m, k)

  case Eventually(p) =>
    exists k: nat ::
      t <= k && Sat(p, m, k)

  case Until(p, q) =>
    (forall k: nat ::
      t <= k ==> Sat(p, m, k))
    ||
    (exists k: nat ::
      t <= k &&
      Sat(q, m, k) &&
      (forall j: nat ::
        t <= j && j < k ==> Sat(p, m, j)))
}

// valid if it is satisfied at all times in all traces
ghost predicate Valid(f: Formula)
{
  forall m: Trace, t: nat ::
    Sat(f, m, t)
}

// helper: always(p) implies p at the current time
lemma AlwaysImpliesNow(p: Formula)
  ensures Valid(Imp(Always(p), p))
{
  forall m: Trace, t: nat
    ensures Sat(Imp(Always(p), p), m, t)
  {
    if Sat(Always(p), m, t) {
      assert Sat(p, m, t);
    }
  }
}

// helper: eventually(p) implies p at some future time
lemma EventuallyWitness(p: Formula, m: Trace, t: nat)
  requires Sat(Eventually(p), m, t)
  ensures exists k: nat :: t <= k && Sat(p, m, k)
{
  assert Sat(Eventually(p), m, t) ==
    (exists k: nat :: t <= k && Sat(p, m, k));
}
