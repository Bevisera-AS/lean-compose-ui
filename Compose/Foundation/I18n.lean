module

public import Compose.Foundation.I18n.Plural
public meta import Compose.Foundation.I18n.Plural
public import Compose.Runtime.Composer
public meta import Compose.Runtime.Composer
public import Compose.Runtime.State
public meta import Compose.Runtime.State
public import Sdl.Locale
public meta import Sdl.Locale

public section

namespace Compose

/-!
# Locale resolution

The framework half of i18n: which language the app should speak. The
string tables themselves stay app-land and *typed* — a record with one
value per user-facing string and one `def` per locale, so a missing
translation is a compile error, not a runtime fallback:

```lean
structure S where
  start : String
  sessions : Int → String

def S.en : S := { start := "Start", sessions := fun n =>
  I18n.plural (I18n.PluralRule.en n) s!"{n} sessions" (one := some "1 session") }
def S.vi : S := { start := "Bắt đầu", sessions := fun n => s!"{n} phiên" }

-- in composition (recomposes on OS language changes):
let strs := if (← resolveLocale #[⟨"vi"⟩]) == some ⟨"vi"⟩ then S.vi else S.en
```

`preferredLocales` is shell-owned state (seeded at bootstrap, refreshed on
SDL's `localeChanged`), so language switches restyle the running app.
-/

namespace I18n

/-- A language tag: lowercase ISO-639 language, optional uppercase ISO-3166
region. -/
structure LocaleTag where
  language : String
  region : Option String := none
  deriving BEq, Repr, Inhabited, Hashable

namespace LocaleTag

/-- Parse `"pt-BR"` / `"pt_BR"` / `"pt"` (case-normalizing). -/
def parse (s : String) : LocaleTag :=
  match s.replace "_" "-" |>.splitOn "-" with
  | lang :: region :: _ =>
    { language := lang.toLower
      region := if region.isEmpty then none else some region.toUpper }
  | _ => { language := s.toLower }

#guard parse "pt-BR" == { language := "pt", region := some "BR" }
#guard parse "pt_br" == { language := "pt", region := some "BR" }
#guard parse "EN" == { language := "en" }

/-- From SDL's locale record. -/
def ofSdl (l : Sdl.Locale) : LocaleTag :=
  { language := l.language.toLower, region := l.country.map (·.toUpper) }

/-- The language's plural rule (`root` for languages the table doesn't
carry — extend the match as translations land). -/
def pluralRule (t : LocaleTag) : PluralRule :=
  match t.language with
  | "en" => PluralRule.en
  | "cs" => PluralRule.cs
  | "pt" => PluralRule.pt
  | "vi" => PluralRule.vi
  | _ => PluralRule.root

end LocaleTag

/-- RFC-4647-flavored lookup: walk the user's `preferred` order; take an
exact language+region hit, else the first `available` sharing the
language. `none` when no preference matches (caller falls back to its
default language). -/
def bestMatch (preferred available : Array LocaleTag) : Option LocaleTag := do
  for p in preferred do
    if available.contains p then
      return p
    if let some t := available.find? (·.language == p.language) then
      return t
  none

#guard bestMatch #[⟨"pt", some "BR"⟩] #[⟨"en", none⟩, ⟨"pt", none⟩]
  == some ⟨"pt", none⟩
#guard bestMatch #[⟨"en", some "US"⟩] #[⟨"en", none⟩] == some ⟨"en", none⟩
#guard bestMatch #[⟨"fr", none⟩, ⟨"vi", none⟩] #[⟨"en", none⟩, ⟨"vi", none⟩]
  == some ⟨"vi", none⟩
#guard bestMatch #[⟨"pt", some "BR"⟩] #[⟨"pt", some "PT"⟩, ⟨"pt", some "BR"⟩]
  == some ⟨"pt", some "BR"⟩
#guard bestMatch #[⟨"fr", none⟩] #[⟨"en", none⟩] == none
#guard bestMatch #[] #[⟨"en", none⟩] == none

end I18n

/-- Shell-owned preferred locales: seeded at bootstrap, refreshed on SDL's
`localeChanged` (Android emits it on per-app/system language changes). -/
initialize preferredLocalesState : MutableState (Array I18n.LocaleTag) ←
  MutableState.create #[]

/-- Refresh `preferredLocalesState` from SDL (best effort — platforms
without locale data keep the current value). Called by the shell. -/
def refreshPreferredLocales : IO Unit := do
  try
    preferredLocalesState.set ((← Sdl.getPreferredLocales).map .ofSdl)
  catch _ => pure ()

/-- The user's preferred locales, live: readers recompose when the OS
language list changes while the app runs. -/
def preferredLocales : Composable (Array I18n.LocaleTag) :=
  preferredLocalesState.get

/-- The best `available` tag for the current user preference (`none` = use
your default language). Live, like `preferredLocales`. -/
def resolveLocale (available : Array I18n.LocaleTag) :
    Composable (Option I18n.LocaleTag) :=
  return I18n.bestMatch (← preferredLocales) available

end Compose

end
