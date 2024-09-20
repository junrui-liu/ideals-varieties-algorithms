# Ideals, Varieties, and Algorithms

Implemented:
- Extended Euclidean algorithm for Z
- An EDSL for building polynomial expressions
  - normalize expressions using the generalized [Horner's method](https://en.wikipedia.org/wiki/Horner's_method)
- Order-polymorphic representation of polynomials
  - a polynomial is represented as a nested map: (var -> exponent) -> coefficient
  - the monomial order is polymorphic using a comparator witness
  - currently variables and fields are passed as functor arguments. How to be polymorphic in those types as well (is it worth it)?
- Orderings:
  - lexicographic
  - graded lexicographic
  - graded reverse lexicographic
- Basic algebras on multivariate polynomials
  - +, -, *
  - long division (rephrased in functional style)
- Gröbner basis
  - Buchberger's fixed-point algorithm
