scry-isa
=============================

todo

## MSRV Policy

This crate's _Minimum Supported Rust Version_ (MSRV) depends on which features are enabled.

The _Base MSRV_ is 1.90. It applies when no features are enabled and is the lowest possible MSRV.
Enabling the following features increases the MSRV to the stated version:

_No features currently increase the MSRV beyond the base._

Enabling features not on the above list doesn't increase the MSRV.

Increasing the Base MSRV or the MSRV of any specific existing feature is a breaking change and will be accompanied by a major version bump. 
Adding new features doesn't count as a breaking change, even if they are enabled by default and thereby increase the commulative MSRV of the default features.

Only the minimal versions of this crate's direct and transitive dependencies are guaranteed to work with the MSRV.

## Changelog

This project adheres to [Semantic Versioning.](https://semver.org/spec/v2.0.0.html)

[changelog_body]

This changelog format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/) and shows only the changes since the previous version.
[See the full changelog](https://github.com/Emoun/duplicate/blob/master/CHANGELOG.md) for changes to all released versions.

#### License

<sup>
Licensed under either of <a href="LICENSE-APACHE">Apache License, Version
2.0</a> or <a href="LICENSE-MIT">MIT license</a> at your option.
</sup>
