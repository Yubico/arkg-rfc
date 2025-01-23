# pqARKG-H: An extension of pqARKG for hierarchical keys

This is a pre-draft of a security proof reduction for pqARKG-H.
If initial peer review is favorable, we intend to rewrite this document using more appropriate typesetting.


## Abstract

Hierarchical Deterministic Keys [[HDK-rfc-id][HDK-rfc-id]] is a draft specification
using key blinding techniques including ARKG [[ARKG-rfc-id][ARKG-rfc-id]]
to create hierarchies of keys all derived from a single base secret key,
in such a way that new public keys can be generated without access to the base secret key
and only the base secret key needs to be kept in a secure environment.
The WebAuthn "sign" extension [[webauthn-sign][webauthn-sign]] is an initiative
to introduce general-purpose hardware-based signing capabilities to the [Web Authentication API][webauthn],
including signing using private keys derived using ARKG.

However, when ARKG is used in HDK, the ARKG procedures as currently specified [[ARKG-rfc-id][ARKG-rfc-id]]
would require an invocation of `ARKG-Derive-Private-Key` for each HDK layer.
With the WebAuthn "sign" extension, this would mean requiring a WebAuthn ceremony and user gesture for each layer.

The ARKG construction in [[ARKG-rfc-id][ARKG-rfc-id]] is based upon pqARKG [[Wilson][wilson]],
a post-quantum compatible construction of the original ARKG [[Frymann2020][frymann2020]].
This document proposes pqARKG-H, an extension of pqARKG for better compatibility with hierarchical keys.
pqARKG-H enables any number of HDK layers
without increasing the number of calls to the secure environment holding the base secret key.

pqARKG-H retains the key security properties of pqARKG,
which we demonstrate by reducing pqARKG to pqARKG-H in the msKS security proof for pqARKG.


## pqARKG

Here we repeat the definition of pqARKG and its msKS security experiment [[Wilson][wilson]].
The instance parameters are a key blinding scheme `Delta`,
a key encapsulation mechanism (KEM) `Pi`
and a pseudo-random function `PRF` outputting blinding factors in the domain of `Delta`.

pqARKG is defined as the following suite of procedures:

```
Setup(1^lambda):
  1. return pp = (Delta, Pi, PRF)

Check(pp, sk', pk'):
  1. return Delta.Check(sk', pk')

KeyGen(pp):
  1. (sk_Delta, pk_Delta) <-$ Delta.KeyGen()
  2. (sk_Pi, pk_Pi)       <-$ Pi.KeyGen()
  3. return sk = (sk_Delta, sk_Pi), pk = (pk_Delta, pk_Pi)

DerivePK(pp, pk = (pk_Delta, pk_Pi), aux):
  1. (c, k) <-$ Pi.Encaps(pk_Pi)
  2. tau <- PRF(k, aux)
  3. pk' <- Delta.BlindPK(pk_Delta, tau)
  4. return pk', cred = (c, aux)

DeriveSK(pp, sk = (sk_Delta, sk_Pi), cred = (c, aux)):
  1. k <- Pi.Decaps(sk_Pi, c)
  2. tau <- PRF(k, aux)
  3. return Delta.BlindSK(sk_Delta, tau)
```

The msKS security experiment for pqARKG is as follows:

```
Exp^{msKS}_{pqARKG,A}:
  1. pp <- Setup(1^lambda)
  2. PKList <- Empty
  3. SKList <- Empty
  4. (sk, pk) <-$ KeyGen()
  5. (sk*, pk*, cred*) <-$ A^{O_pk', O_sk'}(pp, pk)
  6. sk' <- DeriveSK(pp, sk, cred*)
  7. return Check(sk*, pk*)
  8.    AND Check(sk', pk*)
  9.    AND (c*, aux*) not in SKList

O_pk'(aux):
  1. (c, k) <-$ Pi.Encaps(pk_Pi)
  2. tau <- PRF(aux)
  3. pk' <- Delta.BlindPK(pk_Delta, tau)
  4. PKList <- PKList union {(pk', (c, aux))}
  5. return pk', (c, aux)

O_sk'(c, aux):
  1. if (~, (c, aux)) not in PKList then return Failure
  2. SKList <- SKList union {(c, aux)}
  3. k <- Pi.Decaps(sk_Pi, c)
  4. ck <- PRF(k, aux)
  5. return Delta.BlindSK(sk_Delta, ck)
(Here we have corrected a misprint in Exp^{msKS}_{pqARKG,A}, which wrote tau in place of k on line 3 of O_sk')

Equivalently, O_pk' and O_sk' may be written as:

O_pk'(aux):
  1. (pk', cred) <- DerivePK(pp, pk, aux)
  2. PKList <- PKList union {(pk', cred)}
  3. return pk', cred

O_sk'(c, aux):
  1. if (~, (c, aux)) not in PKList then return Failure
  2. SKList <- SKList union {(c, aux)}
  5. return DeriveSK(pp, sk, (c, aux))
```


## pqARKG-H

Here we define our modified pqARKG-H scheme and a corresponding msKS security experiment.

A new parameter `b` is added to the `DerivePK` and `DeriveSK` functions.
This `b` is an additional blinding factor in the key blinding scheme `Delta`,
allowing the ARKG subordinate party (the party generating public keys) to add any number of additional blinding layers
on top of the one performed by the ARKG delegating party (the party holding the ARKG private seed).
To prevent choosing `b = -tau` so that it cancels the blinding factor `tau`
computed in step 2 of `DeriveSK` of pqARKG, this `b` is also mixed into the PRF arguments to compute `tau`.
This disrupts any algebraic relationship between `b` and `tau`,
thus preventing the subordinate party from extracting the private seed `sk` by a malicious choice of `b`.

The new argument to the PRF is however not `b` directly,
but a blinded public key `pk^b_Delta`incorporating the blinding factor `b`.
This enables the subordinate party to prove to an external auditor that a public key was generated using pqARKG-H
without having to disclose `b`.
This is desirable if the subordinate party does not wish to reveal
the relationship with keys from other branches of an HDK tree which might be used for unrelated purposes;
knowing `b` would enable the auditor to unblind the derived public key `pk'` to reveal the root public seed `pk`.
Instead, the auditor may receive `k` and `aux` and recompute steps 3-5 of `DerivePK` with `pk=pk^b_Delta` and `b=0`,
the identity blinding factor,
and thus be convinced that `pk'` was generated from the public seed `pk^b_Delta`.

Finally, the `DeriveSK` function of pqARKG-H also receives the public seed as a new parameter `pk`
in order to reconstruct the same PRF output as `DerivePK`.
This `pk` parameter may be eliminated in instantiations where `pk` can be computed from `sk`.

pqARKG-H requires three additional properties of the the key blinding scheme `Delta`:

 1. There exists an _identity blinding factor_, denoted `0`,
    such that `Delta.BlindPK(pk, 0) = pk` and `Delta.BlindSK(sk, 0) = sk` for all `pk` and `sk`.
 2. `Delta` supports _public key unblinding_ in addition to private key unblinding:
    A function `Delta.UnblindPK(pk, b)` such that `Delta.UnblindPK(Delta.BlindPK(pk, b), b) = pk` for all `pk` and `b`.
 3. `Delta` is _commutative_ in the blinding factor:
    `Delta.BlindPK(Delta.BlindPK(pk, a), b) = Delta.BlindPK(Delta.BlindPK(pk, b), a)`
    and `Delta.BlindSK(Delta.BlindSK(sk, a), b) = Delta.BlindSK(Delta.BlindSK(sk, b), a)`
    for all `pk`, `sk`, `a` and `b`.

pqARKG-H is defined as the following suite of procedures:

```
Setup(1^lambda):      same as pqARKG
Check(pp, sk', pk'):  same as pqARKG
KeyGen(pp):           same as pqARKG

DerivePK(pp, pk = (pk_Delta, pk_Pi), b, aux):
  1. (c, k) <-$ Pi.Encaps(pk_Pi)
  2. pk^b_Delta <- Delta.BlindPK(pk_Delta, b)
  3. tau <- PRF(k, pk^b_Delta, aux)
  4. pk' <- Delta.BlindPK(pk^b_Delta, tau)
  5. return pk', cred = (c, aux)

DeriveSK(pp, pk = (pk_Delta, pk_Pi), sk = (sk_Delta, sk_Pi), b, cred = (c, aux)):
  1. k <- Pi.Decaps(sk_Pi, c)
  2. pk^b_Delta <- Delta.BlindPK(pk_Delta, b)
  3. tau <- PRF(k, pk^b_Delta, aux)
  4. sk^b_Delta <- Delta.BlindSK(sk_Delta, b)
  5. return Delta.BlindSK(sk^b_Delta, tau)
```

Note that if `Delta.BlindSK(sk, b)` is linear in `b`,
then steps 4-5 of `DeriveSK` may be optimized as `4. return Delta.BlindSK(sk_Delta, b + tau)`.

We also modify the msKS security experiment accordingly,
resulting in the security experiment `Exp^{msKS}_{pqARKG-H,B}`.
The main difference is that the adversary `B` also returns the value `b*` to be used as the `b` argument to `DeriveSK`.
The public and private key oracles `O_pk'` and `O_sk'` are also updated to include the `b` parameter
and the additional blinding step.
Finally, the check against `B` trivially querying `O_sk'` for a solution
is relaxed to forbid only the exact combination of `b*` and `cred*` returned as the solution.

```
Exp^{msKS}_{pqARKG-H,B}:
  1. pp <- Setup(1^lambda)
  2. PKList <- Empty
  3. SKList <- Empty
  4. (sk, pk) <-$ KeyGen()
  5. (sk*, pk*, b*, cred*) <-$ B^{O_pk', O_sk'}(pp, pk)
  6. sk' <- DeriveSK(pp, pk, sk, b*, cred*)
  7. return Check(sk*, pk*)
  8.    AND Check(sk', pk*)
  9.    AND (b*, (c*, aux*)) not in SKList

O_pk'(c, aux):
  1. (pk', cred) <- DerivePK(pp, pk, b, aux)
  2. PKList <- PKList union {(pk', cred)}
  3. return pk', cred

O_sk'(b, c, aux):
  1. if (~, (c, aux)) not in PKList then return Failure
  2. SKList <- SKList union {(c, aux)}
  5. return DeriveSK(pp, pk, sk, b, (c, aux))
```


## Reduction of pqARKG to pqARKG-H in msKS security experiment

We now show that pqARKG-H is msKS secure
by showing that an adversary `B` that defeats `Exp^{msKS}_{pqARKG-H,B}`
also defeats `Exp^{msKS}_{pqARKG,A}`.
Given such an adversary `B`,
we construct an adversary `A` that defeats `Exp^{msKS}_{pqARKG,A}` as follows:

```
A^{O_pk', O_sk'}(pp = (Delta, Pi, PRF), pk):
  1. PRF# <- f(k, pkb, aux) = PRF(k, aux)
  2. pp# <- (Delta, Pi, PRF#)
  3. O_pk'# <- f(b, aux):
       1. (pk', (c, ~)) <-$ O_pk'(aux)
       2. pk'# <- Delta.BlindPK(pk', b)
       3. return (pk'#, (c, aux))
  4. O_sk'# <- f(b, c, aux):
       1. sk' <- O_sk'(c, aux)
       2. return Delta.BlindSK(sk', b)
  5. (sk*#, pk*#, b*#, cred*#) <-$ B^{O_pk'#, O_sk'#}(pp#, pk)
  6. sk* <- Delta.UnblindSK(sk*#, b*#)
  7. pk* <- Delta.UnblindPK(pk*#, b*#)
  8. return (sk*, pk*, cred*#)
```

When invoked, this adversary `A` simply invokes the given adversary `B` with its own challenge.
The PRF given in the `pp` input to `A` is adapted to the signature expected by `B`
by simply adding a parameter `pkb` which is ignored when forwarding to the provided PRF.
Because `B` defeats `Exp^{msKS}_{pqARKG-H,B}` given any PRF, `B` must also succeed given this relaxed PRF.

The `O_pk'` and `O_sk'` oracles are similarly adapted for `B` by performing the additional blinding with the `b` argument.
Because the PRF forwarded to `B` ignores its `pkb` argument,
pqARKG-H will produce the same `tau` on line 3 of its `DerivePK` and `DeriveSK` functions
as pqARKG does on line 2 of its `DerivePK` and `DeriveSK` functions.

We see that this adversary passes the checks on lines 7-9 of `Exp^{msKS}_{pqARKG,A}`:

- `Check(sk*, pk*)` succeeds because:

  `sk* = Delta.UnblindSK(sk*#, b*#)` and `pk* = Delta.UnblindPK(pk*#, b*#)`.
  Because `B` defeats `Exp^{msKS}_{pqARKG-H,B}`,
  then `sk*#` and `pk*#` pass the `Check(sk*, pk*)` on line 7 of `Exp^{msKS}_{pqARKG-H,B}`.
  Therefore `Check(sk*, pk*)` must also pass by the definitions of unblinding and unique blinding.

- `Check(sk', pk*)` succeeds because:

  First, observe that
  `sk' = DeriveSK(pp, sk, cred*) = Delta.BlindSK(sk_Delta, PRF(Pi.Decaps(sk_Pi, c*), aux*))` where `cred* = (c*, aux*)`.

  Because `B` defeats `Exp^{msKS}_{pqARKG-H,B}`,
  the `sk'` on line 6 of `Exp^{msKS}_{pqARKG-H,B}` passes `Check(sk', pk*)` on line 8 of `Exp^{msKS}_{pqARKG-H,B}`.
  Let `sk'#` be an alias of this `sk'`.
  We then have:

  ```
  sk'# = DeriveSK(pp#, sk, b*#, cred*#) =   { Expand DeriveSK }
       = Delta.BlindSK(sk^b_Delta, tau) =   { Expand tau }
       = Delta.BlindSK(sk^b_Delta, PRF#(k, pk^b_Delta, aux*#)) =   { PRF# ignores pk^b_Delta and forwards to PRF }
       = Delta.BlindSK(sk^b_Delta, PRF(k, aux*#)) =   { Expand sk^b_Delta }
       = Delta.BlindSK(Delta.BlindSK(sk_Delta, b*#), PRF(k, aux*#)) =   { Expand k }
       = Delta.BlindSK(Delta.BlindSK(sk_Delta, b*#), PRF(Pi.Decaps(sk_Pi, c*#), aux*#)) =   { c* = c*# and aux* = aux*# }
       = Delta.BlindSK(Delta.BlindSK(sk_Delta, b*#), PRF(Pi.Decaps(sk_Pi, c*), aux*)) =   { Commutative blinding }
       = Delta.BlindSK(Delta.BlindSK(sk_Delta, PRF(Pi.Decaps(sk_Pi, c*), aux*)), b*#)
  ```

  combining these facts, we get:
  ```
  Check(sk', pk*) = Check(sk', Delta.UnblindPK(pk*#, b*#)) =   { Blinding correctness }
                  = Check(Delta.BlindSK(sk', b*#), Delta.BlindPK(Delta.UnblindPK(pk*#, b*#), b*#) =   { Blinding cancels unblinding }
                  = Check(Delta.BlindSK(sk', b*#), pk*#) =   { Expand sk' }
                  = Check(Delta.BlindSK(Delta.BlindSK(sk_Delta, PRF(Pi.Decaps(sk_Pi, c*), aux*)), b*#), pk*#) =   { Identify sk'# }
                  = Check(sk'#, pk*#)
  ```

  so `Check(sk', pk*)` succeeds in `Exp^{msKS}_{pqARKG,A}`
  when and precisely when `Check(sk'#, pk*#)` succeeds in `Exp^{msKS}_{pqARKG-H,B}`.
  Since `B` passes its challenge, `A` passes this condition as well.

- `(c*, aux*) not in SKList` succeeds because:

  Because `B` defeats `Exp^{msKS}_{pqARKG-H,B}`,
  the condition `(b*, (c*, aux*)) in SKList` has succeeded in `Exp^{msKS}_{pqARKG-H,B}`.
  Therefore `O_sk'#` has not been called with arguments `(b*, c*, aux*)`,
  therefore `O_sk'` has not been called with arguments `(c*, aux*)`,
  therefore `(c*, aux*) not in SKList` also succeeds.

In conclusion, an adversary `B` that can defeat the msKS property of pqARKG-H
can also be used to also defeat the msKS property of pqARKG.
Thus we conclude that pqARKG-H retains the msKS property of pqARKG.


## Acknowledgements

Thanks to Sander Dijkhuis (@sander) for proposing the construction with mixing `pk^b_Delta` into the PRF instead of `b`.


[ARKG-rfc-id]: https://yubico.github.io/arkg-rfc/draft-bradleylundberg-cfrg-arkg.html
[HDK-rfc-id]: https://www.ietf.org/archive/id/draft-dijkhuis-cfrg-hdkeys-06.html
[frymann2020]: https://eprint.iacr.org/2020/1004
[webauthn-sign]: https://github.com/w3c/webauthn/pull/2078
[webauthn]: https://w3c.github.io/webauthn/
[wilson]: https://uwspace.uwaterloo.ca/items/d1f73f71-e3b2-438c-b261-11632becdbb2
