{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import           Control.Lens
import           Control.Monad
import           Data.Aeson                 as A
import           Data.Aeson.Lens
import           Data.Time
import           Development.Shake
import           Development.Shake.Classes
import           Development.Shake.Forward
import           Development.Shake.FilePath
import           GHC.Generics               (Generic)
import           Slick
import           System.Process             (callCommand)

import qualified Data.Text                  as T
import qualified Data.Text.IO               as T
import qualified Data.ByteString.Lazy.Char8 as BSL8
import qualified Data.HashMap.Strict as HashMap
import Text.Pandoc.Extensions (Extension(..), extensionsFromList)
import qualified Text.Pandoc.Options as Pandoc
import Text.Pandoc.Highlighting
import qualified Data.List as List
import Data.List (sortOn, sortBy)
import Data.Maybe (catMaybes)
import Data.Ord (Down(..))
import Slick.Pandoc (markdownToHTMLWithOpts)
import Text.Pandoc.Definition
import Text.Pandoc.Walk (walk)
import qualified Text.Pandoc as Pandoc
import Text.Pandoc.Writers.HTML (writeHtml5String)
import Text.Pandoc.Readers.Markdown (readMarkdown)
import qualified Data.Text as T
import Data.Char (isAlphaNum, isSpace)
import AgdaSyntaxHighlighting (highlightAgdaCode)

-- Jesus aeson
import Data.Aeson.KeyMap as KM



---Config-----------------------------------------------------------------------

siteMeta :: SiteMeta
siteMeta =
    SiteMeta { siteAuthor = "Callan Mcgill"
             , baseUrl = "https://boarders.github.io"
             , siteTitle = "Callan McGillx"
             , mathstodonHandle = Just "boarders"
             , githubUser = Just "boarders"
             }

outputFolderOld :: FilePath
outputFolderOld = "docs/"

outputFolder :: FilePath
outputFolder = "new/"

--Data models-------------------------------------------------------------------

withSiteMeta :: Value -> Value
withSiteMeta (Object obj) = Object $ KM.union obj siteMetaObj
  where
    Object siteMetaObj = toJSON siteMeta
withSiteMeta _ = error "only add site meta to objects"

data SiteMeta =
    SiteMeta { siteAuthor    :: String
             , baseUrl       :: String -- e.g. https://example.ca
             , siteTitle     :: String
             , mathstodonHandle :: Maybe String -- Without @
             , githubUser    :: Maybe String
             }
    deriving (Generic, Eq, Ord, Show, ToJSON)

-- | Data for the index page
data IndexInfo =
  IndexInfo
    { posts :: [Post]
    } deriving (Generic, Show, FromJSON, ToJSON)

type Tag = String

-- | Data for a blog post
data Post =
    Post { title       :: String
         , author      :: String
         , content     :: String
         , url         :: String
         , date        :: String
         , tags        :: [Tag]
         , description :: String
         , image       :: Maybe String
         , quote       :: Maybe String
         , quoteAuthor :: Maybe String
         , agdaDevelopment :: Maybe String
         , publish     :: Bool
         }
    deriving (Generic, Eq, Ord, Show, FromJSON, ToJSON, Binary)

-- | Config file format for Agda projects
data AgdaProjectConfig =
    AgdaProjectConfig { configName        :: String
                      , configRootModule  :: String
                      , configRootFile    :: String
                      , configDescription :: Maybe String
                      , configPublish     :: Bool
                      }
    deriving (Generic, Eq, Ord, Show, Binary)

instance FromJSON AgdaProjectConfig where
  parseJSON = withObject "AgdaProjectConfig" $ \v -> AgdaProjectConfig
    <$> v .: "name"
    <*> v .: "rootModule"
    <*> v .: "rootFile"
    <*> v .:? "description"
    <*> v .: "publish"

instance ToJSON AgdaProjectConfig where
  toJSON (AgdaProjectConfig n rm rf d p) = object
    [ "name" A..= n
    , "rootModule" A..= rm
    , "rootFile" A..= rf
    , "description" A..= d
    , "publish" A..= p
    ]

-- | Data for an Agda project
data AgdaProject =
    AgdaProject { name        :: String
                , rootModule  :: String
                , rootFile    :: String
                , description :: Maybe String
                , url         :: String
                , htmlFile    :: String
                , projectDir  :: String
                , publish     :: Bool
                }
    deriving (Generic, Eq, Ord, Show, FromJSON, ToJSON, Binary)

-- | Data for the Agda projects index page
data AgdaIndexInfo =
  AgdaIndexInfo
    { projects :: [AgdaProject]
    } deriving (Generic, Show, FromJSON, ToJSON)

data AtomData =
  AtomData { atomTitle    :: String
           , domain       :: String
           , author       :: String
           , posts        :: [Post]
           , currentTime  :: String
           , atomUrl      :: String } deriving (Generic, ToJSON, Eq, Ord, Show)

-- | given a list of posts this will build a table of contents
buildIndex :: [Post] -> Action ()
buildIndex posts' = do
  indexT <- compileTemplate' "site/templates/index.html"
  let sortPosts' = sortPosts posts'
  let indexInfo = IndexInfo {posts = sortPosts'}
      indexHTML = T.unpack $ substitute indexT (withSiteMeta $ toJSON indexInfo)
  writeFile' (outputFolder </> "index.html") indexHTML

-- | Build about page
buildAbout :: Action ()
buildAbout  = do
  aboutT <- compileTemplate' "site/templates/about.html"
  let aboutHTML :: String = T.unpack $ substitute aboutT (toJSON  siteMeta)
  writeFile' (outputFolder </> "about.html") aboutHTML

-- | Find and build all posts
buildPosts :: [AgdaProject] -> HashMap.HashMap T.Text (T.Text, T.Text, T.Text) -> Action [Post]
buildPosts agdaProjects agdaLinkMap = do
  pPaths <- getDirectoryFiles "." ["site/posts//*.md"]
  publishedPosts <- forP pPaths (buildPost agdaProjects agdaLinkMap)
  pure (catMaybes publishedPosts)

-- | Load a post, process metadata, write it to output, then return the post object
-- Detects changes to either post content or template
buildPost :: [AgdaProject]  -- All published proof developments
          -> HashMap.HashMap T.Text (T.Text, T.Text, T.Text)  -- Agda link map
          -> FilePath
          -> Action (Maybe Post)
buildPost agdaProjects agdaLinkMap srcPath = cacheAction ("build" :: T.Text, srcPath) $ do
  liftIO . putStrLn $ "Rebuilding post: " <> srcPath
  postContent <- readFile' srcPath
  -- load post content and metadata as JSON blob
  postData <- convertMarkdown agdaLinkMap . T.pack $ postContent
  let postUrl = T.pack . dropDirectory1 $ srcPath -<.> "html"
      withPostUrl = _Object . at "url" ?~ String postUrl
  -- Add additional metadata we've been able to compute
  let fullPostData = withSiteMeta . withPostUrl $ postData
  template <- compileTemplate' "site/templates/post.html"
  post <- convert fullPostData

  -- Look up Agda development and add URL if found
  let publishedAgdaProjects = Prelude.filter (publish :: AgdaProject -> Bool) agdaProjects
      agdaLookupMap = [(name (p :: AgdaProject), url (p :: AgdaProject)) | p <- publishedAgdaProjects]

  postDataWithAgdaUrl <- case agdaDevelopment (post :: Post) of
    Nothing -> pure fullPostData
    Just devName -> case Prelude.lookup devName agdaLookupMap of
      Nothing -> do
        liftIO $ putStrLn $ "Warning: Agda development '" <> devName <> "' not found for post: " <> title (post :: Post)
        pure fullPostData
      Just devUrl -> pure $ fullPostData & _Object . at "proofDevelopmentUrl" ?~ A.String (T.pack devUrl)

  if publish (post :: Post) then
    do
      liftIO $ putStrLn $ "publishing post: " <> title (post :: Post)
      writeFile' (outputFolder </> T.unpack postUrl) . T.unpack $ substitute template postDataWithAgdaUrl
      liftIO $ putStrLn $ "here"
      pure (Just post)
  else
    do
      liftIO $ putStrLn $ "not publishing post: " <> title (post :: Post)
      pure Nothing

-- | Helper function to convert module name to HTML file name
-- "Foo.Bar.Baz" -> "Foo.Bar.Baz.html"
moduleToHtmlPath :: String -> String
moduleToHtmlPath moduleName = moduleName <> ".html"

-- | Find and build all Agda projects
buildAgdaProjects :: Action [AgdaProject]
buildAgdaProjects = do
  configFiles <- getDirectoryFiles "." ["site/agda/*/agda-project.json"]
  let projectDirs = fmap takeDirectory configFiles
  publishedProjects <- forP projectDirs buildAgdaProject
  pure (catMaybes publishedProjects)

-- | Build a single Agda project
buildAgdaProject :: FilePath -> Action (Maybe AgdaProject)
buildAgdaProject projectPath = do
  let configPath = projectPath </> "agda-project.json"
  configExists <- doesFileExist configPath

  if not configExists
    then do
      liftIO . putStrLn $ "Warning: No agda-project.json in " <> projectPath
      pure Nothing
    else do
      configContent <- readFile' configPath
      projectConfig <- convert (A.decode (BSL8.pack configContent) :: Maybe AgdaProjectConfig)

      let projectName = takeFileName projectPath
          htmlDir = outputFolder </> "agda" </> projectName
          rootFilePath = projectPath </> configRootFile projectConfig
          htmlFileName = moduleToHtmlPath (configRootModule projectConfig)
          htmlOutputPath = htmlDir </> htmlFileName
          projectUrl = "agda/" <> projectName <> "/" <> htmlFileName

      -- Check if output HTML file exists; if not, we need to rebuild
      htmlExists <- doesFileExist htmlOutputPath

      -- Run agda command to generate HTML
      -- Run from the project directory so module names match
      when (not htmlExists) $ do
        liftIO . putStrLn $ "Building Agda project: " <> projectPath
        liftIO . putStrLn $ "Generating Agda HTML for: " <> configName projectConfig
        let agdaCmd = "cd " <> projectPath <> " && /Users/cmcgill21/.cabal/bin/agda --html --html-dir=../../../" <> htmlDir <> " " <> configRootFile projectConfig
        liftIO $ callCommand agdaCmd

      let project = AgdaProject
            { name = configName projectConfig
            , rootModule = configRootModule projectConfig
            , rootFile = configRootFile projectConfig
            , description = configDescription projectConfig
            , url = projectUrl
            , htmlFile = htmlFileName
            , projectDir = projectName
            , publish = configPublish projectConfig
            }

      if publish (project :: AgdaProject)
        then do
          when htmlExists $
            liftIO $ putStrLn $ "Using cached Agda project: " <> name (project :: AgdaProject)
          pure (Just project)
        else do
          liftIO $ putStrLn $ "Not publishing Agda project: " <> name (project :: AgdaProject)
          pure Nothing

-- | Build the Agda projects index page
buildAgdaIndex :: [AgdaProject] -> Action ()
buildAgdaIndex projects = do
  indexT <- compileTemplate' "site/templates/agda-index.html"
  let sortedProjects = sortBy (\a b -> compare (name a) (name b)) projects
      agdaIndexInfo = AgdaIndexInfo { projects = sortedProjects }
      indexHTML = T.unpack $ substitute indexT (withSiteMeta $ toJSON agdaIndexInfo)
  writeFile' (outputFolder </> "agda.html") indexHTML

-- | Copy all static files from the listed folders to their destination
copyStaticFiles :: Action ()
copyStaticFiles = do
    filepaths <- getDirectoryFiles "./site/" ["images//*", "css//*", "js//*"]
    void $ forP filepaths $ \filepath ->
        copyFileChanged ("site" </> filepath) (outputFolder </> filepath)

formatDate :: String -> String
formatDate humanDate = toIsoDate parsedTime
  where
    parsedTime =
      parseTimeOrError True defaultTimeLocale "%b %e, %Y" humanDate :: UTCTime


sortPosts :: [Post] -> [Post]
sortPosts = sortOn (\p -> (Down  (parsedTime . date $ p, title $ p)))
  where
    parsedTime :: String -> UTCTime
    parsedTime d =
      parseTimeOrError True defaultTimeLocale "%b %e, %Y" d :: UTCTime


rfc3339 :: Maybe String
rfc3339 = Just "%H:%M:SZ"

toIsoDate :: UTCTime -> String
toIsoDate = formatTime defaultTimeLocale (iso8601DateFormat rfc3339)

buildFeed :: [Post] -> Action ()
buildFeed posts = do
  now <- liftIO getCurrentTime
  let atomData =
        AtomData
          { atomTitle = siteTitle siteMeta
          , domain = baseUrl siteMeta
          , author = siteAuthor siteMeta
          , posts = mkAtomPost <$> posts
          , currentTime = toIsoDate now
          , atomUrl = "/atom.xml"
          }
  atomTempl <- compileTemplate' "site/templates/atom.xml"
  writeFile' (outputFolder </> "atom.xml") . T.unpack $ substitute atomTempl (toJSON atomData)
    where
      mkAtomPost :: Post -> Post
      mkAtomPost p = p { date = formatDate $ date p }

-- | Specific build rules for the Shake system
--   defines workflow to build the website
buildRules :: Action ()
buildRules = do
  allAgdaProjects <- buildAgdaProjects
  agdaLinkMap <- buildAgdaLinkMap allAgdaProjects
  allPosts <- buildPosts allAgdaProjects agdaLinkMap
  buildIndex allPosts
  buildAgdaIndex allAgdaProjects
  buildAbout
  buildFeed allPosts
  copyStaticFiles


main :: IO ()
main = do
  let shOpts = shakeOptions { shakeVerbosity = Chatty, shakeLintInside = ["\\"]}
  shakeArgsForward shOpts buildRules




-- | Parse Agda HTML files to build a map of definition names to their locations
-- Returns: HashMap DefinitionName (ProjectName, HtmlFile, Anchor)
buildAgdaLinkMap :: [AgdaProject] -> Action (HashMap.HashMap T.Text (T.Text, T.Text, T.Text))
buildAgdaLinkMap projects = do
  maps <- forP projects $ \project -> do
    let htmlPath = outputFolder </> "agda" </> projectDir project </> htmlFile project
    htmlExists <- doesFileExist htmlPath
    if not htmlExists
      then return HashMap.empty
      else do
        htmlContent <- liftIO $ T.readFile htmlPath
        let projectName = T.pack (projectDir project)
            fileName = T.pack (htmlFile project)
            definitions = extractAgdaDefinitions htmlContent
        return $ HashMap.fromList [(name, (projectName, fileName, anchor)) | (name, anchor) <- definitions]
  return $ HashMap.unions maps

-- | Extract definition names and their anchors from Agda HTML
-- Looks for patterns like: <a id="Module.Name"></a>
extractAgdaDefinitions :: T.Text -> [(T.Text, T.Text)]
extractAgdaDefinitions html = go (T.lines html)
  where
    go [] = []
    go (line:rest) =
      case T.breakOn "<a id=\"" line of
        (_, "") -> go rest
        (_, afterId) ->
          case T.stripPrefix "<a id=\"" afterId of
            Nothing -> go rest
            Just after ->
              case T.breakOn "\"" after of
                (idValue, remaining) ->
                  -- Extract the simple name from qualified names (e.g., "Sub.Sub-id" -> "Sub-id")
                  let simpleName = if T.isInfixOf "." idValue
                                   then T.takeWhileEnd (/= '.') idValue
                                   else idValue
                  in if T.null idValue || T.all (\c -> c >= '0' && c <= '9') idValue
                     then go rest  -- Skip numeric IDs
                     else (simpleName, idValue) : go (remaining : rest)

-- | Replace [text](agda-link: Name) and [agda-link: Name] with proper markdown links
-- Uses the Agda link map to resolve names to their locations
preprocessAgdaLinks :: HashMap.HashMap T.Text (T.Text, T.Text, T.Text) -> T.Text -> T.Text
preprocessAgdaLinks linkMap text = go text
  where
    go remaining =
      let customPos = T.breakOn "](agda-link:" remaining
          simplePos = T.breakOn "[agda-link:" remaining
      in case (customPos, simplePos) of
        -- No matches at all
        ((_, ""), (_, "")) -> remaining

        -- Only simple pattern found
        ((_, ""), (beforeSimple, restSimple)) ->
          handleSimplePattern beforeSimple restSimple

        -- Only custom pattern found
        ((beforeCustom, restCustom), (_, "")) ->
          handleCustomPattern beforeCustom restCustom

        -- Both patterns found, use whichever comes first
        ((beforeCustom, restCustom), (beforeSimple, restSimple)) ->
          if T.length beforeCustom < T.length beforeSimple
          then handleCustomPattern beforeCustom restCustom
          else handleSimplePattern beforeSimple restSimple

    handleSimplePattern before rest =
      case T.stripPrefix "[agda-link:" rest of
        Nothing -> before <> "[agda-link:" <> go (T.drop (T.length "[agda-link:") rest)
        Just after ->
          case T.breakOn "]" after of
            (nameWithSpaces, afterBracket) ->
              let name = T.strip nameWithSpaces
              in case HashMap.lookup name linkMap of
                Nothing ->
                  -- Keep the original if not found
                  before <> "[agda-link:" <> nameWithSpaces <> "]" <> go (T.drop 1 afterBracket)
                Just (projectName, fileName, anchor) ->
                  let link = "[" <> name <> "](/agda/" <> projectName <> "/" <> fileName <> "#" <> anchor <> ")"
                  in before <> link <> go (T.drop 1 afterBracket)

    handleCustomPattern beforeParen rest =
      case T.stripPrefix "](agda-link:" rest of
        Nothing -> beforeParen <> "](agda-link:" <> go (T.drop (T.length "](agda-link:") rest)
        Just after ->
          case T.breakOn ")" after of
            (nameWithSpaces, afterCloseParen) ->
              let name = T.strip nameWithSpaces
              in case HashMap.lookup name linkMap of
                Nothing ->
                  -- Keep the original if not found
                  beforeParen <> "](agda-link:" <> nameWithSpaces <> ")" <> go (T.drop 1 afterCloseParen)
                Just (projectName, fileName, anchor) ->
                  -- Extract custom text from before the ](agda-link:
                  case T.breakOnEnd "[" beforeParen of
                    (beforeBracket, customText) ->
                      -- beforeBracket includes the '[', so we need to drop it
                      let before = T.dropEnd 1 beforeBracket
                          link = "[" <> customText <> "](/agda/" <> projectName <> "/" <> fileName <> "#" <> anchor <> ")"
                      in before <> link <> go (T.drop 1 afterCloseParen)

-- | Convert \footnote{...} to Pandoc footnote syntax
preprocessFootnotes :: T.Text -> T.Text
preprocessFootnotes text = go text 1 []
  where
    go :: T.Text -> Int -> [(Int, T.Text)] -> T.Text
    go remaining n accFootnotes =
      case T.breakOn "\\footnote{" remaining of
        (_, "") ->
          -- No more footnotes, append collected footnotes at end
          let footnoteDefs = T.concat [T.pack ("\n\n[^" ++ show i ++ "]: ") <> content | (i, content) <- reverse accFootnotes]
          in remaining <> footnoteDefs
        (before, rest) ->
          case T.stripPrefix "\\footnote{" rest of
            Nothing -> remaining
            Just after ->
              -- Find matching closing brace
              case findClosingBrace after 1 T.empty of
                Nothing -> remaining  -- Malformed, give up
                Just (content, afterBrace) ->
                  let ref = T.pack ("[^" ++ show n ++ "]")
                      newAccFootnotes = (n, content) : accFootnotes
                  in before <> ref <> go afterBrace (n + 1) newAccFootnotes

    -- Find closing brace, handling nested braces
    -- Accumulates content as we go
    findClosingBrace :: T.Text -> Int -> T.Text -> Maybe (T.Text, T.Text)
    findClosingBrace txt depth acc
      | T.null txt = Nothing
      | otherwise =
          let c = T.head txt
              rest = T.tail txt
          in case c of
            '{' -> findClosingBrace rest (depth + 1) (acc `T.snoc` c)
            '}' -> if depth == 1
                   then Just (acc, rest)
                   else findClosingBrace rest (depth - 1) (acc `T.snoc` c)
            _ -> findClosingBrace rest depth (acc `T.snoc` c)

convertMarkdown :: HashMap.HashMap T.Text (T.Text, T.Text, T.Text) -> T.Text -> Action Value
convertMarkdown agdaLinkMap txt = do
  let withAgdaLinks = preprocessAgdaLinks agdaLinkMap txt
      preprocessed = preprocessFootnotes withAgdaLinks
  result <- markdownToHTMLWithOpts readerOptions writerOptions preprocessed
  case result of
    Object obj ->
      case KM.lookup "content" obj of
        Just (String htmlContent) ->
          let enhanced = highlightAgdaCode htmlContent
          in return $ Object $ KM.insert "content" (String enhanced) obj
        _ -> return result
    _ -> return result



syntaxExtensions :: Pandoc.Extensions
syntaxExtensions =
  extensionsFromList
  [Ext_tex_math_dollars, Ext_tex_math_double_backslash, Ext_latex_macros]

pandocExtensions :: Pandoc.Extensions
pandocExtensions =
     Pandoc.enableExtension Ext_smart Pandoc.pandocExtensions
  <> syntaxExtensions


readerOptions :: Pandoc.ReaderOptions
readerOptions = Pandoc.def
    { -- The following option causes pandoc to read smart typography, a nice
      -- and free bonus.
      Pandoc.readerExtensions = pandocExtensions

    }

writerOptions :: Pandoc.WriterOptions
writerOptions = Pandoc.def
    { -- This option causes literate haskell to be written using '>' marks in
      -- html, which I think is a good default.
      Pandoc.writerExtensions = pandocExtensions
    , -- We want to have hightlighting by default, to be compatible with earlier
      -- Hakyll releases
      Pandoc.writerHighlightStyle = Just pygments
    , Pandoc.writerHTMLMathMethod = Pandoc.MathJax ""
    }
