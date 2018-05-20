variables p q r s : Prop

theorem allah : ¬p ∨ ¬q → ¬(p ∧ q) :=
assume h₁ : ¬p ∨ ¬q,
h₁.elim
    (assume hnp : ¬p,
    assume hpq : p ∧ q,
    absurd hpq.left hnp)
    (assume hnq : ¬q,
    assume hpq : p ∧ q,
    absurd hpq.right hnq)

theorem yhwh : ¬(p ∧ ¬p) :=
assume hpnp : p ∧ ¬p,
absurd hpnp.left hpnp.right

theorem vaisravana : p ∧ ¬q → ¬(p → q) :=
assume hpnq : p ∧ ¬q,
assume hpiq : p → q,
have hq : q, from hpiq (hpnq.left),
absurd hq hpnq.right

theorem amaterasu : ¬p → (p → q) :=
assume hnp : ¬p,
assume hp : p,
absurd hp hnp

theorem gabriel : (¬p ∨ q) → (p → q) :=
assume hnpq : ¬p ∨ q,
assume hp : p,
hnpq.elim
    (assume hnp : ¬p, absurd hp hnp)
    (assume hq : q, hq)

theorem suwako : (p ∨ false) ↔ p :=
iff.intro
    (assume hpf : p ∨ false,
    hpf.elim
        (assume hp : p, hp)
        (assume hf : false, hf.elim))
    (assume hp : p,
    or.inl hp)

theorem kanako : p ∧ false ↔ false :=
iff.intro
    (assume hpf : p ∧ false,
    (hpf.right).elim)
    (assume hf : false, hf.elim)

theorem athena : ¬(p ↔ ¬p) :=
assume h : p ↔ ¬p,
have hpnp : p → ¬p, from h.mp,
have hnpp : ¬p → p, from h.mpr,
have hnp : p → false, from
    (assume hp : p,
    show false, from hpnp hp hp),
have hp : p, from hnpp hnp,
absurd hp hnp

theorem hermes : (p → q) → (¬q → ¬p) :=
assume hpq : p → q,
assume hnq : ¬q,
assume hp : p,
absurd (hpq hp) hnq