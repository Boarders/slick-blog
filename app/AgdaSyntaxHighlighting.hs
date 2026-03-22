{-# LANGUAGE OverloadedStrings #-}

module AgdaSyntaxHighlighting
  ( highlightAgdaCode
  , Entity(..)
  , GlobalHighlightState
  ) where

import qualified Data.Text as T
import Data.Char (isAlphaNum, isSpace)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Control.Monad.State
import Data.List (foldl')

-- | Entity types that can be highlighted across code blocks
data Entity = Constructor | Def
  deriving (Eq, Show)

-- | Global state tracking entities across all code blocks
type GlobalHighlightState = HashMap T.Text Entity

-- | State monad for tracking global entities during highlighting
type HighlightM a = State GlobalHighlightState a

-- | Main entry point: highlight Agda code with two-pass approach
-- Pass 1: Collect all constructors from data/record declarations
-- Pass 2: Highlight all code blocks with collected entities
highlightAgdaCode :: T.Text -> T.Text
highlightAgdaCode html = evalState (highlightWithState html) HashMap.empty
  where
    highlightWithState :: T.Text -> HighlightM T.Text
    highlightWithState text = do
      -- Pass 1: Collect constructors from all blocks
      collectConstructors text
      -- Pass 2: Highlight all blocks
      highlightAllBlocks text

-- | Pass 1: Collect all constructors and definitions from code blocks
collectConstructors :: T.Text -> HighlightM ()
collectConstructors text = do
  let blocks = extractCodeBlocks text
  mapM_ collectFromBlock blocks
  where
    collectFromBlock :: T.Text -> HighlightM ()
    collectFromBlock block = do
      let constructorNames = extractConstructorsFromBlock block
          allLocalNames = extractLocalNames block
          -- Filter out constructors from definitions to avoid overwriting
          defNames = filter (`notElem` constructorNames) allLocalNames
      modify $ \state ->
        let s1 = foldl' (\s name -> HashMap.insert name Constructor s) state constructorNames
            s2 = foldl' (\s name -> HashMap.insert name Def s) s1 defNames
        in s2

-- | Extract all code blocks from HTML
extractCodeBlocks :: T.Text -> [T.Text]
extractCodeBlocks text = go text
  where
    go t = case T.breakOn "<code class=\"sourceCode agda\">" t of
      (_, rest) -> case T.stripPrefix "<code class=\"sourceCode agda\">" rest of
        Nothing -> []
        Just after -> case T.breakOn "</code>" after of
          (codeContent, remaining) -> codeContent : go remaining
          _ -> []

-- | Extract constructor names from a single code block
-- Looks for data/record declarations and pattern synonyms
extractConstructorsFromBlock :: T.Text -> [T.Text]
extractConstructorsFromBlock block =
  let lines' = T.lines block
  in extractConstructorsFromLines lines' False
  where
    -- State machine: track whether we're in a data/record constructor zone
    extractConstructorsFromLines :: [T.Text] -> Bool -> [T.Text]
    extractConstructorsFromLines [] _ = []
    extractConstructorsFromLines (line:rest) inConstructorZone
      -- Check for pattern synonyms (pattern _▸_ as a = ...)
      | isPatternDeclaration line =
          extractPatternName line ++ extractConstructorsFromLines rest inConstructorZone
      -- Check if we're entering a constructor zone (data/record ... where)
      | isDataOrRecordDeclaration line =
          extractConstructorsFromLines rest True
      -- If in constructor zone, check if this is a constructor line
      | inConstructorZone =
          if isConstructorLine line
          then extractConstructorName line ++ extractConstructorsFromLines rest True
          else if isUnindentedNonBlank line
               then extractConstructorsFromLines rest False  -- Exit constructor zone
               else extractConstructorsFromLines rest True   -- Continue in zone
      -- Not in constructor zone, keep looking
      | otherwise =
          extractConstructorsFromLines rest False

-- | Check if a line is a pattern synonym declaration
-- Pattern: pattern NAME = ... or pattern _NAME_ ... =
isPatternDeclaration :: T.Text -> Bool
isPatternDeclaration line =
  T.isInfixOf "<span class=\"kw\">pattern</span>" line &&
  T.isInfixOf "=" line

-- | Check if a line is a data or record declaration with where
isDataOrRecordDeclaration :: T.Text -> Bool
isDataOrRecordDeclaration line =
  (T.isInfixOf "<span class=\"kw\">data</span>" line ||
   T.isInfixOf "<span class=\"kw\">record</span>" line) &&
  T.isInfixOf "where" line

-- | Check if a line is a constructor definition (indented line with name followed by :)
isConstructorLine :: T.Text -> Bool
isConstructorLine line =
  case T.breakOn "></a>" line of
    (_, rest) -> case T.stripPrefix "></a>" rest of
      Just after ->
        let trimmed = T.dropWhile isSpace after
        in not (T.null trimmed) && T.head trimmed /= '-'  -- Not a comment
      Nothing -> False

-- | Check if a line is unindented and non-blank (signals end of constructor zone)
-- A line is considered unindented if the first character after ></a> is NOT a space/tab
-- Blank lines (only HTML tags) should not exit the zone
isUnindentedNonBlank :: T.Text -> Bool
isUnindentedNonBlank line =
  case T.breakOn "></a>" line of
    (_, rest) -> case T.stripPrefix "></a>" rest of
      Just after ->
        if T.null after
        then False  -- Empty line
        else
          let firstChar = T.head after
          -- Skip blank lines (where first char is <, meaning closing tags only)
          in firstChar /= ' ' && firstChar /= '\t' && firstChar /= '-' && firstChar /= '<'
      Nothing -> False

-- | Extract pattern synonym name from a line
-- Handles both: pattern NAME = ... and pattern _NAME_ ... =
extractPatternName :: T.Text -> [T.Text]
extractPatternName line =
  -- First check if it's an infix pattern
  case extractInfixPattern line of
    [] -> extractRegularPattern line
    names -> names
  where
    extractInfixPattern :: T.Text -> [T.Text]
    extractInfixPattern l =
      case T.breakOn "<span class=\"kw\">pattern</span>" l of
        (_, rest) -> case T.stripPrefix "<span class=\"kw\">pattern</span>" rest of
          Just after ->
            -- Look for _NAME_ pattern
            case T.breakOn "<span class=\"ot\">_</span>" after of
              (_, rest2) -> case T.stripPrefix "<span class=\"ot\">_</span>" rest2 of
                Just after2 ->
                  let (middle, remainder) = T.span (\c -> c /= '<') after2
                  in if T.isPrefixOf "<span class=\"ot\">_</span>" remainder
                     then [middle]
                     else []
                Nothing -> []
          Nothing -> []

    extractRegularPattern :: T.Text -> [T.Text]
    extractRegularPattern l =
      case T.breakOn "<span class=\"kw\">pattern</span>" l of
        (_, rest) -> case T.stripPrefix "<span class=\"kw\">pattern</span>" rest of
          Just after ->
            let trimmed = T.dropWhile isSpace after
                -- For patterns, grab everything until space, <, or =
                (word, _) = T.span (\c -> not (isSpace c || c == '<' || c == '=')) trimmed
            in if not (T.null word)
               then [word]
               else []
          Nothing -> []

-- | Extract constructor name from a line
extractConstructorName :: T.Text -> [T.Text]
extractConstructorName line =
  -- Try regular constructor pattern first
  case extractRegularConstructor line of
    [] -> extractInfixConstructor line
    names -> names
  where
    extractRegularConstructor :: T.Text -> [T.Text]
    extractRegularConstructor l =
      case T.breakOn "></a>" l of
        (_, rest) -> case T.stripPrefix "></a>" rest of
          Just after ->
            let trimmed = T.dropWhile isSpace after
                (word, remainder) = T.span isIdentChar trimmed
                trimmedRemainder = T.dropWhile isSpace remainder
            in if not (T.null word) &&
                  isIdentStart (T.head word) &&
                  (T.isPrefixOf "<span class=\"ot\">:</span>" trimmedRemainder ||
                   T.isPrefixOf ":" trimmedRemainder)
               then [word]
               else []
          Nothing -> []

    extractInfixConstructor :: T.Text -> [T.Text]
    extractInfixConstructor l =
      case T.breakOn "<span class=\"ot\">_</span>" l of
        (_, rest) -> case T.stripPrefix "<span class=\"ot\">_</span>" rest of
          Just after ->
            let (middle, remainder) = T.span (\c -> c /= '<') after
            in if T.isPrefixOf "<span class=\"ot\">_</span>" remainder &&
                  T.isInfixOf ":" remainder
               then [middle]
               else []
          Nothing -> []

-- | Pass 2: Highlight all code blocks with global state
highlightAllBlocks :: T.Text -> HighlightM T.Text
highlightAllBlocks text = do
  globalState <- get
  return $ processBlocks globalState text
  where
    processBlocks :: GlobalHighlightState -> T.Text -> T.Text
    processBlocks state t =
      case T.breakOn "<code class=\"sourceCode agda\">" t of
        (before, rest) -> case T.stripPrefix "<code class=\"sourceCode agda\">" rest of
          Nothing -> t
          Just after -> case T.breakOn "</code>" after of
            (codeContent, remaining) ->
              let enhanced = highlightSingleBlock state codeContent
              in before <> "<code class=\"sourceCode agda\">" <> enhanced <>
                 processBlocks state remaining
            _ -> t

-- | Highlight a single code block with global and local entities
highlightSingleBlock :: GlobalHighlightState -> T.Text -> T.Text
highlightSingleBlock globalState block =
  let localNames = extractLocalNames block  -- Already excludes constructors
      -- Split global entities by type
      globalConstructors = [name | (name, Constructor) <- HashMap.toList globalState]
      globalDefs = [name | (name, Def) <- HashMap.toList globalState]
      -- Filter out global entities from local names to avoid double-highlighting
      localOnlyNames = filter (\n -> not (HashMap.member n globalState)) localNames
      -- Highlight in order: constructors (cn), global defs (dfn), local defs (dfn), Type (dt)
      withConstructors = highlightConstructors globalConstructors block
      withGlobalDefs = highlightFunctions globalDefs withConstructors
      withLocalDefs = highlightFunctions localOnlyNames withGlobalDefs
      withType = highlightType withLocalDefs
  in withType

-- | Extract local function and type names from a code block
-- This excludes constructors (names inside data/record blocks)
extractLocalNames :: T.Text -> [T.Text]
extractLocalNames block =
  let lines' = T.lines block
  in extractNamesFromLines lines' False
  where
    -- State machine: track whether we're in a data/record constructor zone
    extractNamesFromLines :: [T.Text] -> Bool -> [T.Text]
    extractNamesFromLines [] _ = []
    extractNamesFromLines (line:rest) inConstructorZone
      -- Skip pattern synonym declarations (they're constructors, not functions)
      | isPatternDeclaration line =
          extractNamesFromLines rest inConstructorZone
      -- Check if we're entering a constructor zone (data/record ... where)
      | isDataOrRecordDeclaration line =
          -- Extract the data/record type name itself, then enter constructor zone
          extractDataTypeName line ++ extractNamesFromLines rest True
      -- If in constructor zone, skip constructor names but check for exit
      | inConstructorZone =
          if isUnindentedNonBlank line
          then extractFromLine line ++ extractInfixOperator line ++ extractNamesFromLines rest False
          else extractNamesFromLines rest True  -- Skip names in constructor zone
      -- Not in constructor zone, extract normally
      | otherwise =
          extractFromLine line ++ extractInfixOperator line ++ extractNamesFromLines rest False

-- | Extract function/type names from a line (only when NOT in constructor zone)
extractFromLine :: T.Text -> [T.Text]
extractFromLine line =
  -- Check for regular type signatures
  case T.breakOn "></a>" line of
    (_, rest) -> case T.stripPrefix "></a>" rest of
      Just after ->
        -- Skip leading whitespace before extracting the name
        let trimmed = T.dropWhile isSpace after
            (word, remainder) = T.span isIdentChar trimmed
            trimmedRemainder = T.dropWhile isSpace remainder
        in if not (T.null word) &&
              isIdentStart (T.head word) &&
              (T.isPrefixOf "<span class=\"ot\">:</span>" trimmedRemainder ||
               T.isPrefixOf ":" trimmedRemainder)
           then [word]
           else []
      Nothing -> []

-- | Extract data/record type name from declaration line
extractDataTypeName :: T.Text -> [T.Text]
extractDataTypeName line
  | T.isInfixOf "<span class=\"kw\">data</span>" line =
      maybeToList $ extractAfterKeyword "<span class=\"kw\">data</span>" line
  | T.isInfixOf "<span class=\"kw\">record</span>" line =
      maybeToList $ extractAfterKeyword "<span class=\"kw\">record</span>" line
  | otherwise = []
  where
    maybeToList Nothing = []
    maybeToList (Just x) = [x]

-- | Extract middle part of infix operators like _∘R_ or _/[_]
extractInfixOperator :: T.Text -> [T.Text]
extractInfixOperator line =
  case T.breakOn "<span class=\"ot\">_</span>" line of
    (_, rest) -> case T.stripPrefix "<span class=\"ot\">_</span>" rest of
      Just after ->
        -- Collect everything until we see the closing <span class="ot">_</span>
        case collectUntilClosingUnderscore after T.empty of
          Just (middle, remainder) ->
            -- Check if there's a : after (possibly with other chars like ])
            if T.isInfixOf ":" remainder
               then [middle]
               else []
          Nothing -> []
      Nothing -> []
  where
    -- Collect characters and HTML tags until we find <span class="ot">_</span>
    collectUntilClosingUnderscore :: T.Text -> T.Text -> Maybe (T.Text, T.Text)
    collectUntilClosingUnderscore remaining acc
      | T.null remaining = Nothing
      | T.isPrefixOf "<span class=\"ot\">_</span>" remaining =
          Just (acc, remaining)
      | T.isPrefixOf "<" remaining =
          -- Include HTML tags in the middle part
          case T.breakOn ">" remaining of
            (tag, afterTag) ->
              collectUntilClosingUnderscore (T.drop 1 afterTag) (acc <> tag <> ">")
      | otherwise =
          collectUntilClosingUnderscore (T.tail remaining) (acc `T.snoc` T.head remaining)

-- | Extract name after a keyword (handles parameters before :)
-- Examples: "data Foo :" or "data Bar (x : A) :" or "record Baz :"
extractAfterKeyword :: T.Text -> T.Text -> Maybe T.Text
extractAfterKeyword keyword line =
  case T.breakOn keyword line of
    (_, rest) -> case T.stripPrefix keyword rest of
      Just after ->
        let trimmed = T.dropWhile isSpace after
            (word, remainder) = T.span isIdentChar trimmed
        in if not (T.null word) &&
              isIdentStart (T.head word) &&
              T.isInfixOf ":" remainder  -- Just check : exists somewhere after name
           then Just word
           else Nothing
      Nothing -> Nothing

-- | Highlight constructors with <span class="cn">
highlightConstructors :: [T.Text] -> T.Text -> T.Text
highlightConstructors constructorNames text =
  foldl' highlightConstructor text constructorNames

-- | Highlight a single constructor with <span class="cn">
highlightConstructor :: T.Text -> T.Text -> T.Text
highlightConstructor text name = replaceWord wrapConstructor text name
  where
    wrapConstructor :: T.Text -> T.Text
    wrapConstructor n = "<span class=\"cn\">" <> n <> "</span>"

-- | Highlight functions with <dfn>
highlightFunctions :: [T.Text] -> T.Text -> T.Text
highlightFunctions names text =
  foldl' highlightFunction text names
  where
    highlightFunction :: T.Text -> T.Text -> T.Text
    highlightFunction t name = replaceWord wrapFunction t name

    wrapFunction :: T.Text -> T.Text
    wrapFunction n = "<dfn>" <> n <> "</dfn>"

-- | Highlight Type keyword with <span class="dt">
highlightType :: T.Text -> T.Text
highlightType text = replaceWord wrapType text "Type"
  where
    wrapType :: T.Text -> T.Text
    wrapType n = "<span class=\"dt\">" <> n <> "</span>"

-- | Replace all occurrences of a word with wrapped version
-- Only replaces whole words (surrounded by word boundaries)
replaceWord :: (T.Text -> T.Text) -> T.Text -> T.Text -> T.Text
replaceWord wrapper haystack needle = go haystack
  where
    go text = case T.breakOn needle text of
      (_, "") -> text  -- Not found
      (before, rest) ->
        let after = T.drop (T.length needle) rest
            -- Check if surrounded by word boundaries (not just spaces)
            beforeOk = T.null before || isWordBoundary (T.last before)
            afterOk = T.null after || isWordBoundary (T.head after)
        in if beforeOk && afterOk
           then before <> wrapper needle <> go after
           else before <> needle <> go after

-- | Check if a character is a word boundary
-- Includes spaces, HTML tag markers, parentheses, and other punctuation
isWordBoundary :: Char -> Bool
isWordBoundary c = isSpace c || c `elem` ("<>(){}[].,;:!?\"'`" :: String)

-- | Character classification helpers
isIdentStart :: Char -> Bool
isIdentStart c = isIdentChar c  -- In Agda, any identifier character can start an identifier

isIdentChar :: Char -> Bool
isIdentChar c = isAlphaNum c || c `elem` ("_'-′″‴∘∙×⇒⊎≡≢≤≥≈≃∀∃λΛ∇∆√∑∏∫⊕⊗⊥⊤⊢⊣⊨⊔⊓∪∩⊆⊇⊂⊃∈∉∋∌ℕℤℚℝℂ𝔸𝔹ℙ𝕆𝟙𝟘/[]⟦⟧" :: String)
