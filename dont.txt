Advice that is actually simple to follow and works around some bugs.

# [Unifall](https://github.com/coq/coq/pull/7013)

Don't use `unify x y`, use `let __ := constr:(Logic.eq_refl : x = y) in idtac.`

Don't use `reflexivity`, use `exact Logic.eq_refl`, or if typeclass resolution is desired, `exact (Coq.Classes.RelationClasses.reflexivity _)`.

# Built-in tactics

Don't use `evar (x : T)`, use `let x' := open_constr:(_:T) in pose x' as x.` or just `let x' := open_constr:(_) in pose x' as x.`.

Don't use `intuition`, use `intuition auto`.

Don't use `firstorder`, use `intuition with core`.
