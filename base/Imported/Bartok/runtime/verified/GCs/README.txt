This directory contains BoogiePL code for these verified garbage collectors:
  - MiniMs.bpl:
      miniature verified mark-sweep collector
  - MiniMsRegions.bpl:
      miniature verified mark-sweep collector, using region-based invariants
  - MiniCopyingRegions.bpl:
      miniature verified copying collector, using region-based invariants
  - VerifiedCopyingCollector.bpl:
      practical verified copying collector (x86 code encoded in BoogiePL)
  - VerifiedMarkSweepCollector.bpl:
      practical verified mark-sweep collector (x86 code encoded in BoogiePL)

These can be verified with the April 2008 release of Boogie/Z3, available in the
April 2008 release of Spec# at:

  http://research.microsoft.com/specsharp/

To verify the collectors, type:

\Spec#\bin\Boogie.exe /noinfer MiniMs.bpl
\Spec#\bin\Boogie.exe /noinfer MiniMsRegions.bpl
\Spec#\bin\Boogie.exe /noinfer MiniCopyingRegions.bpl
\Spec#\bin\Boogie.exe /bv:z /noinfer TrustedBitVectorsBuiltin.bpl VerifiedBitVectorsBuiltin.bpl VerifiedBitVectorsBuiltinImpl.bpl
\Spec#\bin\Boogie.exe /bv:z /noinfer Trusted.bpl TrustedBitVectors.bpl VerifiedBitVectorsBuiltin.bpl VerifiedBitVectors.bpl VerifiedBitVectorsImpl.bpl
\Spec#\bin\Boogie.exe /noinfer Trusted.bpl VerifiedBitVectors.bpl VerifiedCommon.bpl VerifiedCopyingCollector.bpl
\Spec#\bin\Boogie.exe /noinfer Trusted.bpl VerifiedBitVectors.bpl VerifiedCommon.bpl VerifiedMarkSweepCollector.bpl

For example, verifying MiniMs.bpl should generate the following Boogie output:

  Boogie program verifier version 0.90, Copyright (c) 2003-2008, Microsoft.

  Boogie program verifier finished with 7 verified, 0 errors



NOTES:

The collectors lack some of the features supported by Bartok's native run-time
system.  In particular, they only collect single-threaded programs, lack full
support for arrays of structs of pointers, and lack support for unsafe code
(e.g. pinning).

We don't yet have a Singularity-compatible version of the small runtime system
that hosts the verified garbage collectors, so the verified collectors don't yet
run on Singularity.  We hope to implement at least a limited
Singularity-compatible version in the not-too-distant future.

The collectors currently assume that Boogie functions are "expand false" by
default.  This default may change in future versions of Boogie, in which case
the function definitions in the collectors will need to be marked explicitly
as "expand false".

Our BoogiePL-to-MASM translator (used for VerifiedCopyingCollector.bpl,
VerifiedMarkSweepCollector.bpl, and VerifiedCommon.bpl) enforces on the
following variable name conventions, where x and X represent any sequence of
letters, digits, and underscores, whose first non-underscore character is a
lower-case letter (for x) or uppercase letter (for X):
  - X is a physical global variable, of type int, or a procedure name
  - x is a physical local variable, of type int, or an inline procedure name
  - $X is a ghost variable, of any type, which the untrusted code may read
  - $x is a ghost variable, of any type, which the untrusted code may read/write
  - ?X is an integer constant
  - ?x is a const variable containing an integer constant
The translator signals an error if the untrusted code tries to write to
$X, ?x or ?X.  In addition, the translator signals an error if the untrusted
code tries to write to the esp register, except as part of a procedure call
or return.  Note that pure function names and pure function parameters are not
bound by these naming conventions.

Boogie verifies the collectors (and their allocators), but we have not (yet)
used Boogie to verify mutators.  The mutator is in charge of choosing abstract
nodes (when calling the allocation procedures) and defining the properties of
abstract nodes, such as numFields and $AbsMem.  To ensure that the collector
can't replace non-GC pointer values (e.g. null, unmanaged pointers)
with GC pointers, the mutator should choose non-word integers to represent
abstract nodes.

