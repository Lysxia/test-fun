# Testable functions

A representation of functions for property testing, featuring
random generation, shrinking and printing.

This package implements the core functionality.
Separate packages integrate it with existing testing frameworks.

- QuickCheck: [quickcheck-higherorder](https://github.com/Lysxia/quickcheck-higherorder)

- Hedgehog: TODO

## References

- [*Shrinking and showing functions*](https://dl.acm.org/citation.cfm?id=2364516),
  by Koen Claessen, Haskell Symposium 2012.

  This package extends that work with support for higher-order functions.

  Other implementations based on that paper can be found in:

  + [*QuickCheck*](https://hackage.haskell.org/package/QuickCheck-2.13.2); in
    particular see the [`Fun`
    type](https://hackage.haskell.org/package/QuickCheck-2.13.2/docs/Test-QuickCheck.html#g:14).

  + [*hedgehog-fn*](https://hackage.haskell.org/package/hedgehog-fn).

## Internal module policy

Modules under `Test.Fun.Internal` are not subject to any versioning policy.
Breaking changes may apply to them at any time.

If something in those modules seems useful, please report it or create a pull
request to export it from an external module.
