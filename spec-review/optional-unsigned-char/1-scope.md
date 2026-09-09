# Review scope

This review covers only `std::optional<unsigned char>` as implemented by
libstdc++ 12. It does not propose a generic `std::optional<T>` specification.

## Operation contracts

The specification registers six operations:

1. construction from `std::nullopt_t` produces a disengaged optional;
2. construction from an `unsigned char` rvalue copies the source byte and
   preserves the source object;
3. construction from an `unsigned char` lvalue copies the source byte and
   preserves the source object;
4. `has_value() const` reports engagement without changing the object;
5. `operator*() const &` requires engagement and returns a reference to the
   byte contained in that optional; and
6. destruction consumes the optional and ends ownership of its contained byte.

The abstract model is either `empty` or `engaged byte`, where `byte` is the
mathematical value represented by an `unsigned char`.

## Selected clients

### Positive: `arbitrary_byte_roundtrip`

Constructs const optionals containing low and high nonzero byte values, checks
engagement, and reads the stored values. This is the ordinary positive example.

### Positive: `rvalue_snapshot_not_alias`

Constructs an optional from an rvalue source, changes the source afterward, and
checks that the optional retained the original value. This exercises source
preservation and independent storage.

### Negative: `reference_outlives_optional`

Keeps a pointer to the contained byte after the optional has been destroyed and
then attempts to read through it. Its proof is intentionally unable to close:
the destructor consumes the representation that justified access to the byte.

## Out of scope

This packet does not cover a generic element type, optional-to-optional copy or
move construction, assignment, `reset`, `emplace`, exceptions, comparisons, or
monadic operations.
