{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE DuplicateRecordFields #-}

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

import qualified Data.HashMap.Lazy as HML
import qualified Data.Text                  as T
import Text.Pandoc.Extensions (Extension(..), extensionsFromList)
import qualified Text.Pandoc.Options as Pandoc
import Text.Pandoc.Highlighting
import Slick.Pandoc (markdownToHTMLWithOpts)
import Data.List (sortOn)
import Data.Ord (Down(..))

---Config-----------------------------------------------------------------------

siteMeta :: SiteMeta
siteMeta =
    SiteMeta { siteAuthor = "Callan Mcgill"
             , baseUrl = "https://boarders.github.io"
             , siteTitle = "Callan McGill"
             , twitterHandle = Nothing
             , githubUser = Just "boarders"
             }

outputFolder :: FilePath
outputFolder = "docs/"

--Data models-------------------------------------------------------------------

withSiteMeta :: Value -> Value
withSiteMeta (Object obj) = Object $ HML.union obj siteMetaObj
  where
    Object siteMetaObj = toJSON siteMeta
withSiteMeta _ = error "only add site meta to objects"

data SiteMeta =
    SiteMeta { siteAuthor    :: String
             , baseUrl       :: String -- e.g. https://example.ca
             , siteTitle     :: String
             , twitterHandle :: Maybe String -- Without @
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
         }
    deriving (Generic, Eq, Ord, Show, FromJSON, ToJSON, Binary)

data AtomData =
  AtomData { title        :: String
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

-- | Find and build all posts
buildPosts :: Action [Post]
buildPosts = do
  pPaths <- getDirectoryFiles "." ["site/posts//*.md"]
  forP pPaths buildPost

-- | Load a post, process metadata, write it to output, then return the post object
-- Detects changes to either post content or template
buildPost :: FilePath -> Action Post
buildPost srcPath = cacheAction ("build" :: T.Text, srcPath) $ do
  liftIO . putStrLn $ "Rebuilding post: " <> srcPath
  postContent <- readFile' srcPath
  -- load post content and metadata as JSON blob
  postData <- convertMarkdown . T.pack $ postContent
  let postUrl = T.pack . dropDirectory1 $ srcPath -<.> "html"
      withPostUrl = _Object . at "url" ?~ String postUrl
  -- Add additional metadata we've been able to compute
  let fullPostData = withSiteMeta . withPostUrl $ postData
  template <- compileTemplate' "site/templates/post.html"
  writeFile' (outputFolder </> T.unpack postUrl) . T.unpack $ substitute template fullPostData
  convert fullPostData

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
sortPosts = sortOn (Down . parsedTime . date)
  where
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
          { title = siteTitle siteMeta
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
  allPosts <- buildPosts
  buildIndex allPosts
  buildFeed allPosts
  copyStaticFiles


main :: IO ()
main = do
  let shOpts = shakeOptions { shakeVerbosity = Chatty, shakeLintInside = ["\\"]}
  shakeArgsForward shOpts buildRules



convertMarkdown :: T.Text -> Action Value
convertMarkdown = markdownToHTMLWithOpts readerOptions writerOptions



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
