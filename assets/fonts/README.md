# Bundled fonts

Roboto v3.016 static weights (Regular, Medium, Bold), from
[googlefonts/roboto-3-classic](https://github.com/googlefonts/roboto-3-classic/releases/tag/v3.016),
licensed under the SIL Open Font License 1.1 (see `OFL.txt`).

`NotoEmoji-Regular.ttf` is the monochrome variable-weight Noto Emoji from
[google/fonts (ofl/notoemoji)](https://github.com/google/fonts/tree/main/ofl/notoemoji),
also OFL 1.1 — the sized emoji fallback (`Compose/Ui/Text/Fonts.lean`;
platform color-emoji fonts either aren't rasterizable — Android's COLRv1 —
or aren't present, so outlines beat blanks).

This is the framework's default UI font family (the same family Compose's
Material theme uses). `FontStore` falls back to platform system fonts for
glyphs Roboto lacks.
