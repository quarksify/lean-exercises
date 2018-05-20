open classical
variables p q r s : Prop

theorem corsica : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
assume h : p → r ∨ s,
by_cases
    (assume h1 : p,
        (h h1).elim
            (assume hr : r, or.inl (assume hp : p, hr))
            (assume hs : s, or.inr (assume hp : p, hs)))
    (assume h1 : ¬p, or.inl (assume hp : p, absurd hp h1))

theorem sardinia : ¬(p ∧ q) → ¬p ∨ ¬q :=
assume hpqf : p ∧ q → false,
by_cases
    (assume h1 : p,
    by_cases
        (assume h2 : q, (hpqf ⟨h1, h2⟩).elim)
        (assume h2 : ¬q, or.inr h2)
        )
    (assume h1 : ¬p, or.inl h1)

theorem trivium : p ∨ ¬p := em p

theorem sicilia : ¬(p → q) → p ∧ ¬q :=
assume hpqf : (p → q) → false,
by_cases
    (assume h1 : p, 
    by_cases
        (assume h2 : q,
        have hpq : p → q, from (assume hp : p, h2),
        absurd hpq hpqf)
        (assume h2 : ¬q, ⟨h1, h2⟩))
    (assume h1 : ¬p,
    by_cases
        (assume h2 : q,
        have hpq : p → q, from (assume hp : p, h2),
        absurd hpq hpqf)
        (assume h2 : ¬q,
        have hpq : p → q, from (assume hp : p, absurd hp h1),
        absurd hpq hpqf))

theorem creta : (p → q) → (¬p ∨ q) :=
assume hpq : p → q,
by_cases
    (assume h1 : p, or.inr (hpq h1))
    (assume h1 : ¬p, or.inl h1)

theorem ilium : (¬q → ¬p) → (p → q) :=
assume hnqnp : ¬q → ¬p,
assume hp : p,
by_cases
    (assume h1 : q, h1)
    (assume h1 : ¬q, absurd hp (hnqnp h1))

#check ilium (p → q) p

theorem roma : (((p → q) → p) → p) :=
assume h1 : ((p → q) → p),
by_cases
    (assume h2 : p → q, h1 h2)
    (assume h2 : (p → q) → false, sorry
    -- h2 (p → q) p h1
        )