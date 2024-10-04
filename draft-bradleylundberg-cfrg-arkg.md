---
stand_alone: true
ipr: trust200902

title: 'TEMPORARY: COSE algorithms for two-party signing'
abbrev: "TBD"
lang: en
category: info

docname: draft-bradleylundberg-cfrg-arkg-latest
submissiontype: IETF  # also: "independent", "editorial", "IAB", or "IRTF"
number:
date:
consensus: true
v: 3
area: "TBD"
workgroup: "TBD"
keyword:
 - KDF
venue:
  group: "TBD"
  type: "TBD"
  github: "Yubico/arkg-rfc"


author:
- role: editor
  fullname: Emil Lundberg
  organization: Yubico
  street: Kungsgatan 44
  city: Stockholm
  country: SE
  email: emil@emlun.se

normative:
  fully-spec-algs:
    title: Fully-Specified Algorithms for JOSE and COSE
    target: https://datatracker.ietf.org/doc/draft-ietf-jose-fully-specified-algorithms/
    author:
    - name: Michael B. Jones
      ins: M.B. Jones
      org: Self-Issued Consulting
      email: michael_b_jones@hotmail.com
      uri: https://self-issued.info
    date: 2024
  IANA.cose:
  IANA.cose:
  RFC2104:
  RFC4949:
  RFC5869:
  RFC6090:
  RFC7748:
  RFC8032:
  RFC8610:
  RFC8812:
  RFC9052:
  RFC9380:
  SEC1:
    target: http://www.secg.org/sec1-v2.pdf
    author:
    - org: Certicom Research
    date: 2009
    title: 'SEC 1: Elliptic Curve Cryptography'
  SEC2:
    target: http://www.secg.org/sec2-v2.pdf
    author:
    - org: Certicom Research
    date: 2010
    title: 'SEC 2: Recommended Elliptic Curve Domain Parameters'

informative:
  ARKG:
    target: https://datatracker.ietf.org/doc/draft-bradleylundberg-cfrg-arkg/
    title: The Asynchronous Remote Key Generation (ARKG) algorithm
    date: 2024
  BIP32:
    target: https://github.com/bitcoin/bips/blob/master/bip-0032.mediawiki
    title: BIP 32 Hierarchical Deterministic Wallets
    author:
    - name: Pieter Wuille
    date: 2012
  COSE-Hash-Envelope:
    title: COSE Hash Envelope
    target: https://datatracker.ietf.org/doc/draft-ietf-cose-hash-envelope/
    author:
    - name: Orie Steele
      ins: O. Steele
      org: Transmute
      email: orie@transmute.industries
    - name: Steve Lasker
      org: DataTrails
      email: steve.lasker@datatrails.ai
    - name: Henk Birkholz
      org: Fraunhofer SIT
      email: henk.birkholz@ietf.contact
    date: 2024
  Clermont:
    target: https://www.cryptoplexity.informatik.tu-darmstadt.de/media/crypt/teaching_1/theses_1/Sebastian_Clermont_Thesis.pdf
    author:
    - name: Sebastian A. Clermont
      org: "Technische Universität Darmstadt"
    date: 2022
    title: "Post Quantum Asynchronous Remote Key Generation. Master's thesis"
  WebAuthn-Recovery:
    author:
    - name: Emil Lundberg
    - name: Dain Nilsson
    title: "WebAuthn recovery extension: Asynchronous delegated key generation without shared secrets. GitHub"
    date: 2019
    target: https://github.com/Yubico/webauthn-recovery-extension
  Frymann2020:
    author:
    - name: Nick Frymann
    - name: Daniel Gardham
    - name: Franziskus Kiefer
    - name: Emil Lundberg
    - name: Mark Manulis
    - name: Dain Nilsson
    title: "Asynchronous Remote Key Generation: An Analysis of Yubico's Proposal for W3C WebAuthn. CCS '20: Proceedings of the 2020 ACM SIGSAC Conference on Computer and Communications Security"
    date: 2020
    target: https://eprint.iacr.org/2020/1004
  Frymann2023:
    author:
    - name: Nick Frymann
    - name: Daniel Gardham
    - name: Mark Manulis
    title: Asynchronous Remote Key Generation for Post-Quantum Cryptosystems from Lattices. 2023 IEEE 8th European Symposium on Security and Privacy
    date: 2023
    target: https://eprint.iacr.org/2023/419
  Shoup:
    author:
    - name: Victor Shoup
      org: IBM Zurich Research Lab
    title: A Proposal for an ISO Standard for Public Key Encryption (version 2.0)
    date: 2001
    target: https://www.shoup.net/papers/iso-2.pdf
  Wilson:
    author:
    - name: Spencer MacLaren Wilson
      org: University of Waterloo,
    title: "Post-Quantum Account Recovery for Passwordless Authentication. Master's thesis"
    date: 2023
    target: http://hdl.handle.net/10012/19316



--- abstract

TODO

THIS DOCUMENT IS A TEMPORARY PROTOTYPE AREA FOR ILLUSTRATING SOME IDEAS FOR DISCUSSION.
THESE IDEAS ARE PLANNED TO MOVE TO A DIFFERENT DOCUMENT WHEN MORE MATURE.



--- middle

{:emlun: source="Emil"}

# Introduction

Most COSE algorithm identifiers are meant for annotating a cryptogram
with how a consumer may interpret it,
but do not record all details of how the cryptogram was created since that is usually irrelevant for the consumer.
The algorithm identifiers defined in this document are the opposite -
they define interfaces between two parties co-operating to create a cryptogram together,
but are unsuitable for annotating the resulting cryptogram with how the consumer should interpret it.

A primary use case for this is executing a signature algorithm split between two parties,
such as a software application and a discrete hardware security module (HSM) holding the private key.
In particular, since the data link between them may have limited bandwidth,
it may not be practical to send the entire original message to the HSM.
Instead, since most signature algorithms begin with digesting the message
into a fixed-length intermediate input, this initial digest can be computed by the software application
while the HSM computes the rest of the signature algorithm on the digest.

Since different signature algorithms digest the message in different ways
and at different stages of the algorithm,
there is no unambiguous way to define a division point generically for every possible signature algorithm.
Therefore, this document defines algorithm identifiers encoding, for each concrete signature algorithm,
which steps of the signature algorithm are performed by the _digester_ (e.g., software application)
and which are performed by the _signer_ (e.g., HSM).
In general, the _signer_ holds exclusive control of the signing private key.

Note that these algorithm identifiers do not define new "pre-hashed" variants of the base signature algorithm,
nor an intermediate "hash envelope" data structure such as that defined in [COSE-Hash-Envelope].
Rather these are the same signature algorithms that would typically be executed by a single party,
but split into two stages.
The resulting signatures are identical in structure to those computed by a single party,
and can be verified using the same verification procedure
without additional steps to preprocess the signed data.
However some signature algorithms, for example PureEdDSA [RFC8032] or ML-DSA [FIPS-204],
cannot be split in this way and therefore cannot be assigned a two-party signing algorithm identifier.
If such a signature algorithm defines a "pre-hashed" variant, such as Ed25519ph [RFC8032] or HashML-DSA [FIPS-204],
that algorithm may be assigned a two-party signing algorithm identifier instead.


# Two-party signing algorithms

This section defines divisions of signing algorithm steps between a _digester_ and a _signer_
in a two-party signing protocol,
and assigns algorithm identifiers to these algorithm divisions.
The _digester_ performs the first part of the divided algorithm and does not have access to the signing private key,
while the _signer_ performs the second part of the divided algorithm and has access to the signing private key.
For signing algorithms that format the message to insert domain separation tags,
this message formatting is also performed by the _signer_.

The algorithm identifiers defined in this document SHALL NOT appear in COSE structures
other than COSE_Key_Ref (see {{cose-key-refs}}).
They are meant only for coordination between _digester_ and _signer_ in a two-party signing protocol.
External representations of used keys and resulting signatures
SHALL use the corresponding conventional algorithm identifiers instead.
These are listed in the "Base algorithm" column in the tables defining two-party signing algorithm identifiers.


## ECDSA {#ecdsa-2p}

Two-party ECDSA [FIPS-186-5] uses the following division between _digester_ and _signer_
of the steps of the ECDSA signature generation algorithm [FIPS-186-5]:

- The signing procedure is defined in [Section 6.4.1 of FIPS-186-5].
- The _digester_ performs step 1 of the signing procedure.
- The message input to the _signer_ is the value _H_ defined in the signing procedure.
- The _signer_ resumes the signing procedure from step 2.

The following algorithm identifiers are defined:

| Name      | COSE Value | Base algorithm | Description |
| --------- | ---------- | -------------- | ----------- |
| ESP256-2p | TBD        | ESP256         | ESP256 [fully-spec-algs] divided as defined in {{ecdsa-2p}} of this document |
| ESP384-2p | TBD        | ESP384         | ESP384 [fully-spec-algs] divided as defined in {{ecdsa-2p}} of this document |
| ESP512-2p | TBD        | ESP512         | ESP512 [fully-spec-algs] divided as defined in {{ecdsa-2p}} of this document |


## HashEdDSA {#eddsa-2p}

Two-party HashEdDSA [RFC8032] uses the following division between _digester_ and _signer_
of the steps of the HashEdDSA signing algorithm [RFC8032]:

- HashEdDSA is a combination of the EdDSA signing procedure and the PureEdDSA signing procedure.
  The EdDSA signing procedure is defined in the first paragraph of {{Section 3.3 of RFC8032}}.
  The PureEdDSA signing procedure is defined in the second paragraph of {{Section 3.3 of RFC8032}}.
- The _digester_ computes the value `PH(M)` defined in the EdDSA signing procedure.
- The message input to the _signer_ is the value `PH(M)` defined in the EdDSA signing procedure.
  This value is represented as `M` in the PureEdDSA signing procedure.
- The _signer_ executes the PureEdDSA signing procedure,
  where the value denoted `M` in the PureEdDSA signing procedure
  takes the value denoted `PH(M)` in the EdDSA signing procedure.

PureEdDSA [RFC8032] cannot be divided in this way
since such a division would require that the _digester_ has access to the private key.

The following algorithm identifiers are defined:

| Name         | COSE Value | Base algorithm | Description |
| ------------ | ---------- | -------------- | ----------- |
| Ed25519ph-2p | TBD        | Ed25519ph      | Ed25519ph [fully-spec-algs] divided as defined in {{eddsa-2p}} of this document (NOTE: Ed25519ph not yet defined) |
| Ed448ph-2p   | TBD        | Ed448ph        | Ed448ph [fully-spec-algs] divided as defined in {{eddsa-2p}} of this document (NOTE: Ed448ph not yet defined) |


## HashML-DSA {#ml-dsa-2p}

Two-party HashML-DSA [FIPS-204] uses the following division between _digester_ and _signer_
of the steps of the HashML-DSA.Sign algorithm:

- The signing procedure is defined in [Section 5.4.1 of FIPS-204].
- The _digester_ computes the value PH<sub>_M_</sub> defined in steps 10 to 22 of the signing procedure.
- The message input to the _signer_ is the value PH<sub>_M_</sub> defined in the signing procedure.
  The additional _ctx_ input must also be transmitted to the _signer_.
  This may for example be done using the `ctx (-1)` parameter of a `COSE_Key_Ref` with `kty (1): Ref-ML-DSA (TBD)`
  (see {{cose-key-types-reg}} and {{cose-key-type-params-reg}}).
- The _signer_ executes all steps of the signing procedure
  except the steps 13, 16, 19 or similar that compute the value PH<sub>_M_</sub>.
  Note in particular that the _signer_ generates the value _rnd_ in steps 5-8
  and constructs the value _M'_ in step 23.

The "pure" ML-DSA version [FIPS-204] cannot be divided in this way
because of how the embedding of the _ctx_ and _tr_ values is constructed
in `ML-DSA.Sign` and `ML-DSA.Sign_Internal`.
A division like the above for HashML-DSA would move control of this embedding from the _signer_ to the _digester_.
This would break the domain separation enforced by the embedding
and possibly enable signature malleability attacks or protocol confusion attacks.

The following algorithm identifiers are defined:

| Name             | COSE Value | Base algorithm | Description |
| ---------------- | ---------- | -------------- | ----------- |
| HashML-DSA-44-2p | TBD        | HashML-DSA-44  | HashML-DSA-44 [TODO] divided as defined in {{ml-dsa-2p}} of this document (NOTE: HashML-DSA-44 not yet defined) |
| HashML-DSA-65-2p | TBD        | HashML-DSA-65  | HashML-DSA-65 [TODO] divided as defined in {{ml-dsa-2p}} of this document (NOTE: HashML-DSA-65 not yet defined) |
| HashML-DSA-87-2p | TBD        | HashML-DSA-87  | HashML-DSA-87 [TODO] divided as defined in {{ml-dsa-2p}} of this document (NOTE: HashML-DSA-87 not yet defined) |


# COSE key reference types {#cose-key-refs}

While keys used by many other algorithms can usually be referenced by a single atomic identifier,
such as that used in the `kid` parameter in a COSE_Key object or in the unprotected header of a COSE_Recipient,
some signature algorithms use additional parameters to the signature generation
beyond the signing private key and message to be signed.
For example, ML-DSA [FIPS-204] has the additional parameter _ctx_
and `ARKG-Derive-Secret-Key` [ARKG] has the parameters `kh` and `info` in addition to the private key.

While these additional parameters are simple to provide to the API of the signing procedure
in a single-party context,
in a two-party context these additional parameters also need to be conveyed from _digester_ to _signer_.
For this purpose we define new COSE key types, collectively called "COSE key reference types".
This enables defining a unified, algorithm-agnostic protocol between _digester_ and _signer_,
rather than requiring a distinct protocol for each signature algorithm for the sake of conveying algorithm-specific parameters.

A COSE key reference is a COSE_Key object whose `kty` value is defined to represent a reference to a key.
The `kid` parameter MUST be present when `kty` is a key reference type.
These requirements are encoded in the CDDL [RFC8610] type `COSE_Key_Ref`:

~~~cddl
COSE_Key_Ref = COSE_Key .within {
  1 ^ => $COSE_kty_ref   ; kty: Any reference type
  2 ^ => any,            ; kid is required
  any => any,            ; Any other entries allowed by COSE_Key
}
~~~

The following CDDL example represents a reference to an ML-DSA-65 key,
along with the value of the _ctx_ parameter to ML-DSA.Sign [FIPS-204]:

~~~cddl
{
  1: TBD,      ; kty: Ref-ML-DSA
               ; kid: Opaque identifier of the ML-DSA key
  2: h'92bc2bfa738f5bb07803fb9c0c58020791acd29fbe253baa7a03ac84f4b26d44',

  3: TBD,      ; alg: ML-DSA-65

               ; ctx argument to ML-DSA.Sign
  -1: 'Example application info',
}
~~~


The following CDDL example represents a reference to a key derived by `ARKG-P256ADD-ECDH`
and restricted for use with the ESP256 [fully-spec-algs] signature algorithm:

~~~cddl
{
  1: -65538,   ; kty: Ref-ARKG-derived
               ; kid: Opaque identifier of ARKG-pub
  2: h'60b6dfddd31659598ae5de49acb220d8
       704949e84d484b68344340e2565337d2',
  3: -9,       ; alg: ESP256

               ; ARKG-P256ADD-ECDH key handle
               ; (HMAC-SHA-256-128 followed by
                  SEC1 uncompressed ECDH public key)
  -1: h'ae079e9c52212860678a7cee25b6a6d4
        048219d973768f8e1adb8eb84b220b0ee3
          a2532828b9aa65254fe3717a29499e9b
          aee70cea75b5c8a2ec2eb737834f7467
          e37b3254776f65f4cfc81e2bc4747a84',

               ; info argument to ARKG-Derive-Private-Key
  -2: 'Example application info',
}
~~~


# IANA Considerations {#IANA}

## COSE Key Types Registrations {#cose-key-types-reg}

This section registers the following values in the IANA "COSE Key Types" registry [IANA.COSE].

- Name: Ref-OKP
  - Value: TBD (Requested assignment -1)
  - Description: Reference to a key pair of key type "OKP"
  - Capabilities: \[kty(-1), crv\]
  - Reference: {{cose-key-refs}} of this document

- Name: Ref-EC2
  - Value: TBD (Requested assignment -2)
  - Description: Reference to a key pair of key type "EC2"
  - Capabilities: \[kty(-1), crv\]
  - Reference: {{cose-key-refs}} of this document

- Name: Ref-ML-DSA
  - Value: TBD
  - Description: Reference to a key pair of key type "ML-DSA"
  - Capabilities: \[kty(TBD), ctx\]
  - Reference: TBD

These registrations add the following choices to the CDDL [RFC8610] type socket `$COSE_kty_ref`:

~~~cddl
$COSE_kty_ref /= -1       ; Value TBD
$COSE_kty_ref /= -2       ; Value TBD
$COSE_kty_ref /= TBD      ; Value TBD
~~~


## COSE Key Type Parameters Registrations {#cose-key-type-params-reg}

This section registers the following values in the IANA "COSE Key Type Parameters" registry [IANA.COSE].

- Key Type: TBD (Ref-ML-DSA)
  - Name: ctx
  - Label: -1
  - CBOR Type: bstr
  - Description: ctx argument to ML-DSA.Sign or HashML-DSA.Sign
  - Reference: TBD


--- back

# Document History

THIS IS A TEMPORARY DOCUMENT JUST TO MOCK UP THE IDEA
