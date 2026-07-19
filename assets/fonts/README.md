# Bundled fonts

Roboto v3.016 static weights (Regular, Medium, Bold), from
[googlefonts/roboto-3-classic](https://github.com/googlefonts/roboto-3-classic/releases/tag/v3.016),
licensed under the SIL Open Font License 1.1 (see `OFL.txt`).

`TwemojiMozilla.ttf` is [Twemoji Mozilla v0.7.0](https://github.com/mozilla/twemoji-colr)
(unchanged), the COLRv0 build of Twitter's Twemoji — artwork
[CC-BY 4.0](https://creativecommons.org/licenses/by/4.0/) © Twitter, Inc.
and other contributors, font code MIT © Mozilla Foundation. It is the
primary sized emoji fallback (`Compose/Ui/Text/Fonts.lean`): COLR v0 is
the one color-font format FreeType composites natively, so it renders in
color everywhere we target (platform color-emoji fonts either aren't
rasterizable — Android's COLRv1 — or aren't present).

`NotoEmoji-Regular.ttf` is the monochrome variable-weight Noto Emoji from
[google/fonts (ofl/notoemoji)](https://github.com/google/fonts/tree/main/ofl/notoemoji),
also OFL 1.1 — the second emoji fallback, covering codepoints newer than
the color font (outlines beat blanks).

This is the framework's default UI font family (the same family Compose's
Material theme uses). `FontStore` falls back to platform system fonts for
glyphs Roboto lacks.
