
include "LTL.dfy"

// A1: ◇p <==> ¬□¬p

lemma A1Sound(p: Formula)
  ensures Valid(Iff(Eventually(p), Not(Always(Not(p)))))
{
  forall m: Trace, t: nat
    ensures Sat(Iff(Eventually(p), Not(Always(Not(p)))), m, t)
  {
    // direction 1: Eventually(p) => Not(Always(Not(p)))
    if Sat(Eventually(p), m, t) {
        EventuallyWitness(p, m, t);

        ghost var k: nat :|
            t <= k && Sat(p, m, k);
        assert !Sat(Not(p), m, k);
        assert !Sat(Always(Not(p)), m, t);
        assert Sat(Not(Always(Not(p))), m, t);
    }
    // direction 2: Not(Always(Not(p))) => Eventually(p)
    if Sat(Not(Always(Not(p))), m, t) {
      assert !Sat(Always(Not(p)), m, t);

      assert !(forall k: nat ::
        t <= k ==> Sat(Not(p), m, k));

      assert exists k: nat ::
        t <= k && !Sat(Not(p), m, k);

      var k: nat :|
        t <= k && !Sat(Not(p), m, k);

      assert Sat(p, m, k);
      assert Sat(Eventually(p), m, t);
    }

    assert Sat(
      Iff(Eventually(p), Not(Always(Not(p)))),
      m, t
    );
  }
}


// A2: □(p -> q) -> (□p -> □q)

lemma A2Sound(p: Formula, q: Formula)
  ensures Valid(
    Imp(
      Always(Imp(p, q)),
      Imp(Always(p), Always(q))
    )
  )
{
  forall m: Trace, t: nat
    ensures Sat(
      Imp(
        Always(Imp(p, q)),
        Imp(Always(p), Always(q))
      ),
      m, t
    )
  {
    // assume □(p -> q) and □p
    if Sat(Always(Imp(p, q)), m, t) &&
       Sat(Always(p), m, t)
    {
      // show q holds at every future time
      forall k: nat | t <= k
        ensures Sat(q, m, k)
      {
        // □(p -> q) gives p -> q at time k
        assert Sat(Imp(p, q), m, k);

        // □p gives p at time k
        assert Sat(p, m, k);

        // Modus ponens: p and (p -> q) give q
        assert Sat(q, m, k);
      }

      // therefore □q holds
      assert Sat(Always(q), m, t);
    }

    // therefore the entire implication holds
    assert Sat(
      Imp(
        Always(Imp(p, q)),
        Imp(Always(p), Always(q))
      ),
      m, t
    );
  }
}


// A3: ○¬p <==> ¬○p

lemma A3Sound(p: Formula)
  ensures Valid(
    Iff(Next(Not(p)), Not(Next(p)))
  )
{
  forall m: Trace, t: nat
    ensures Sat(
      Iff(Next(Not(p)), Not(Next(p))),
      m, t
    )
  {
    // expand the left side: ○¬p
    assert Sat(Next(Not(p)), m, t)
      == Sat(Not(p), m, t + 1);

    assert Sat(Not(p), m, t + 1)
      == !Sat(p, m, t + 1);

    // expand the right side: ¬○p
    assert Sat(Next(p), m, t)
      == Sat(p, m, t + 1);

    assert Sat(Not(Next(p)), m, t)
      == !Sat(Next(p), m, t);

    // both sides equal !Sat(p, m, t + 1)
    assert Sat(Next(Not(p)), m, t)
      == Sat(Not(Next(p)), m, t);

    // therefore the equivalence holds
    assert Sat(
      Iff(Next(Not(p)), Not(Next(p))),
      m, t
    );
  }
}


// A4: ○(p -> q) -> (○p -> ○q)

lemma A4Sound(p: Formula, q: Formula)
  ensures Valid(
    Imp(
      Next(Imp(p, q)),
      Imp(Next(p), Next(q))
    )
  )
{
  forall m: Trace, t: nat
    ensures Sat(
      Imp(
        Next(Imp(p, q)),
        Imp(Next(p), Next(q))
      ),
      m, t
    )
  {
    // assume ○(p -> q) and ○p
    if Sat(Next(Imp(p, q)), m, t) &&
       Sat(Next(p), m, t)
    {
      // unfold the Next operator
      assert Sat(Imp(p, q), m, t + 1);
      assert Sat(p, m, t + 1);

      // apply modus ponens at time t + 1
      assert Sat(q, m, t + 1);

      // therefore ○q holds
      assert Sat(Next(q), m, t);
    }

    // the entire implication is valid
    assert Sat(
      Imp(
        Next(Imp(p, q)),
        Imp(Next(p), Next(q))
      ),
      m, t
    );
  }
}


// A5: □p -> (p ∧ ○p ∧ ○□p)

lemma A5Sound(p: Formula)
  ensures Valid(
    Imp(
      Always(p),
      And(p, And(Next(p), Next(Always(p))))
    )
  )
{
  forall m: Trace, t: nat
    ensures Sat(
      Imp(
        Always(p),
        And(p, And(Next(p), Next(Always(p))))
      ),
      m, t
    )
  {
    if Sat(Always(p), m, t) {

      // part 1: p holds now
      assert Sat(p, m, t);

      // part 2: p holds at the next time step
      assert Sat(p, m, t + 1);
      assert Sat(Next(p), m, t);

      // part 3: □p holds at the next time step
      forall k: nat | t + 1 <= k
        ensures Sat(p, m, k)
      {
        assert t <= k;
        assert Sat(p, m, k);
      }

      // p is always true starting at t + 1
      assert Sat(Always(p), m, t + 1);

      // therefore ○□p holds
      assert Sat(Next(Always(p)), m, t);

      // combine the three properties
      assert Sat(
        And(p, And(Next(p), Next(Always(p)))),
        m, t
      );
    }

    // the entire implication holds
    assert Sat(
      Imp(
        Always(p),
        And(p, And(Next(p), Next(Always(p))))
      ),
      m, t
    );
  }
}

// helper lemma for A6:
// if p holds now and is preserved at every step, then p holds at any future time k.
lemma A6Induction(
  p: Formula,
  m: Trace,
  t: nat,
  k: nat
)
  requires t <= k
  requires Sat(p, m, t)
  requires Sat(Always(Imp(p, Next(p))), m, t)
  ensures Sat(p, m, k)
  decreases k - t
{
  if k == t {
    // base case: p is true at time t
    assert Sat(p, m, k);
  } else {
    // inductive step: k > t
    assert t <= k - 1;

    // by induction, p holds at k - 1
    A6Induction(p, m, t, k - 1);
    assert Sat(p, m, k - 1);

    // the preservation rule holds at k - 1
    assert Sat(Imp(p, Next(p)), m, k - 1);

    // since p holds at k - 1, Next(p) holds there
    assert Sat(Next(p), m, k - 1);

    // next(p) at k - 1 means p at k
    assert Sat(p, m, k);
  }
}


// A6: □(p -> ○p) -> (p -> □p)

lemma A6Sound(p: Formula)
  ensures Valid(
    Imp(
      Always(Imp(p, Next(p))),
      Imp(p, Always(p))
    )
  )
{
  forall m: Trace, t: nat
    ensures Sat(
      Imp(
        Always(Imp(p, Next(p))),
        Imp(p, Always(p))
      ),
      m, t
    )
  {
    // assume □(p -> ○p) and p
    if Sat(Always(Imp(p, Next(p))), m, t) &&
       Sat(p, m, t)
    {
      // show p holds at every future time
      forall k: nat | t <= k
        ensures Sat(p, m, k)
      {
        A6Induction(p, m, t, k);
      }

      // therefore □p holds
      assert Sat(Always(p), m, t);
    }

    // the complete implication is valid
    assert Sat(
      Imp(
        Always(Imp(p, Next(p))),
        Imp(p, Always(p))
      ),
      m, t
    );
  }
}


// A7: □p -> (p U q)
// U uses weak-until semantics

lemma A7Sound(p: Formula, q: Formula)
  ensures Valid(
    Imp(Always(p), Until(p, q))
  )
{
  forall m: Trace, t: nat
    ensures Sat(
      Imp(Always(p), Until(p, q)),
      m, t
    )
  {
    // assume p is always true
    if Sat(Always(p), m, t) {

      // unfold the meaning of Always(p)
      assert forall k: nat ::
        t <= k ==> Sat(p, m, k);

      // this satisfies the first case of weak until
      assert
        (forall k: nat ::
          t <= k ==> Sat(p, m, k))
        ||
        (exists k: nat ::
          t <= k && Sat(q, m, k) &&
          (forall j: nat ::
            t <= j && j < k ==> Sat(p, m, j)));

      // therefore p U q holds
      assert Sat(Until(p, q), m, t);
    }

    // therefore the entire implication is valid
    assert Sat(
      Imp(Always(p), Until(p, q)),
      m, t
    );
  }
}


lemma A8StepBack(
  p: Formula, q: Formula,
  m: Trace, t: nat
)
  requires Sat(p, m, t)
  requires Sat(Until(p, q), m, t + 1)
  ensures Sat(Until(p, q), m, t)
{
  if forall k: nat ::
       t + 1 <= k ==> Sat(p, m, k)
  {
    forall k: nat | t <= k
      ensures Sat(p, m, k)
    {
      if k == t {
        assert Sat(p, m, k);
      } else {
        assert t + 1 <= k;
        assert Sat(p, m, k);
      }
    }
  } else {
    assert exists k: nat ::
      t + 1 <= k &&
      Sat(q, m, k) &&
      (forall j: nat ::
        t + 1 <= j && j < k ==> Sat(p, m, j));

    ghost var k: nat :|
      t + 1 <= k &&
      Sat(q, m, k) &&
      (forall j: nat ::
        t + 1 <= j && j < k ==> Sat(p, m, j));

    forall j: nat | t <= j && j < k
      ensures Sat(p, m, j)
    {
      if j == t {
        assert Sat(p, m, j);
      } else {
        assert t + 1 <= j;
        assert Sat(p, m, j);
      }
    }

    assert exists k0: nat ::
      t <= k0 &&
      Sat(q, m, k0) &&
      (forall j: nat ::
        t <= j && j < k0 ==> Sat(p, m, j));
  }

  assert Sat(Until(p, q), m, t);
}


lemma A8StepForward(
  p: Formula, q: Formula,
  m: Trace, t: nat
)
  requires Sat(Until(p, q), m, t)
  requires !Sat(q, m, t)
  ensures Sat(p, m, t)
  ensures Sat(Until(p, q), m, t + 1)
{
  // expand the weak-until definition explicitly
  assert
    (forall k: nat ::
      t <= k ==> Sat(p, m, k))
    ||
    (exists k: nat ::
      t <= k && Sat(q, m, k) &&
      (forall j: nat ::
        t <= j && j < k ==> Sat(p, m, j)));

  if forall k: nat ::
       t <= k ==> Sat(p, m, k)
  {
    // case 1: p holds forever
    assert Sat(p, m, t);

    forall k: nat | t + 1 <= k
      ensures Sat(p, m, k)
    {
      assert t <= k;
      assert Sat(p, m, k);
    }

    assert Sat(Until(p, q), m, t + 1);
  } else {
    // case 2: q eventually holds
    assert exists k: nat ::
      t <= k && Sat(q, m, k) &&
      (forall j: nat ::
        t <= j && j < k ==> Sat(p, m, j));

    ghost var k: nat :|
      t <= k && Sat(q, m, k) &&
      (forall j: nat ::
        t <= j && j < k ==> Sat(p, m, j));

    // q is false now, so its witness must be later
    assert k != t;
    assert t + 1 <= k;

    // p must hold at the current time
    assert Sat(p, m, t);

    // p continues to hold until the witness
    forall j: nat | t + 1 <= j && j < k
      ensures Sat(p, m, j)
    {
      assert t <= j;
      assert Sat(p, m, j);
    }

    assert exists k0: nat ::
      t + 1 <= k0 && Sat(q, m, k0) &&
      (forall j: nat ::
        t + 1 <= j && j < k0 ==> Sat(p, m, j));

    assert Sat(Until(p, q), m, t + 1);
  }
}


// A8: (p U q) <==> (q OR (p AND Next(p U q)))
// q OR r is encoded as Not(q) -> r


lemma A8Sound(p: Formula, q: Formula)
  ensures Valid(
    Iff(
      Until(p, q),
      Imp(Not(q), And(p, Next(Until(p, q))))
    )
  )
{
  forall m: Trace, t: nat
    ensures Sat(
      Iff(
        Until(p, q),
        Imp(Not(q), And(p, Next(Until(p, q))))
      ),
      m, t
    )
  {
    // name the left and right sides
    ghost var left :=
      Sat(Until(p, q), m, t);

    ghost var right :=
      Sat(
        Imp(Not(q), And(p, Next(Until(p, q)))),
        m, t
      );

    
    // direction 1: left -> right
    if left {
    if !Sat(q, m, t) {
        A8StepForward(p, q, m, t);

        assert Sat(p, m, t);
        assert Sat(Until(p, q), m, t + 1);
        assert Sat(Next(Until(p, q)), m, t);

        assert Sat(
        And(p, Next(Until(p, q))), m, t
        );
    }

    // unfold the negation
    assert Sat(Not(q), m, t) == !Sat(q, m, t);

    // unfold the implication
    assert right ==
        (Sat(Not(q), m, t) ==>
        Sat(
            And(p, Next(Until(p, q))),
            m, t
        ));

    // the implication holds:
    // either q is true, or the conjunction holds
    assert right;
    }


    // direction 2: right -> left
    if right {
      if Sat(q, m, t) {

        // q holds now, so k = t is a witness
        assert forall j: nat ::
          t <= j && j < t ==> Sat(p, m, j);

        assert exists k: nat ::
          t <= k &&
          Sat(q, m, k) &&
          (forall j: nat ::
            t <= j && j < k ==> Sat(p, m, j));

        assert Sat(Until(p, q), m, t);

      } else {

        // q is false, so Not(q) is true
        assert Sat(Not(q), m, t);

        // unfold the implication
        assert right ==
          (Sat(Not(q), m, t) ==>
            Sat(
              And(p, Next(Until(p, q))),
              m, t
            ));

        // extract the conjunction
        assert Sat(
          And(p, Next(Until(p, q))),
          m, t
        );

        // unfold the conjunction
        assert Sat(
          And(p, Next(Until(p, q))),
          m, t
        ) ==
          (Sat(p, m, t) &&
           Sat(Next(Until(p, q)), m, t));

        // extract both components
        assert Sat(p, m, t);
        assert Sat(Next(Until(p, q)), m, t);

        // unfold the Next operator
        assert Sat(Next(Until(p, q)), m, t)
          == Sat(Until(p, q), m, t + 1);

        assert Sat(Until(p, q), m, t + 1);

        // apply the verified helper lemma
        A8StepBack(p, q, m, t);
      }

      assert left;
    }

    // establish both directions
    assert left ==> right;
    assert right ==> left;
    assert left == right;

    // conclude A8
    assert Sat(
      Iff(
        Until(p, q),
        Imp(Not(q), And(p, Next(Until(p, q))))
      ),
      m, t
    );
  }
}
