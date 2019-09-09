{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE IncoherentInstances #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Text.Html
-- Copyright   :  (c) Andy Gill and OGI, 1999-2001
-- License     :  BSD-style (see the file libraries/base/LICENSE)
--
-- Maintainer  :  Andy Gill <andy@galconn.com>
-- Stability   :  provisional
-- Portability :  portable
--
-- An Html combinator library
--
-----------------------------------------------------------------------------

module Html.Html (
      module Html.Html,
      ) where


import Control.DeepSeq
import GHC.Generics hiding (Rep)

import Test.QuickCheck hiding (Fun)
import Test.Dragen2

import qualified Html.BlockTable as BT

infixr 3 `above`  -- combining table cells
infixr 4 `beside`  -- combining table cells
infixr 2 `combine`  -- combining Html
infixr 7 `nest`   -- nesting Html
infixl 8 !    -- adding optional arguments

deriving instance Generic Char
deriving instance Generic HtmlAttr
deriving instance Generic HtmlElement
deriving instance Generic Html

instance NFData HtmlAttr
instance NFData HtmlElement
instance NFData Html

-- A important property of Html is that all strings inside the
-- structure are already in Html friendly format.
-- For example, use of &gt;,etc.

data HtmlElement
{-
 -    ..just..plain..normal..text... but using &copy; and &amb;, etc.
 -}
      = HtmlString String
{-
 -    <thetag {..attrs..}> ..content.. </thetag>
 -}
      | HtmlTag {                   -- tag with internal markup
              markupTag      :: String,
              markupAttrs    :: [HtmlAttr],
              markupContent  :: Html
              }
      deriving Show
{- These are the index-value pairs.
 - The empty string is a synonym for tags with no arguments.
 - (not strictly HTML, but anyway).
 -}


data HtmlAttr = HtmlAttr String String


newtype Html = Html { getHtmlElements :: [HtmlElement] }

-- Read MARKUP as the class of things that can be validly rendered
-- inside MARKUP tag brackets. So this can be one or more Html's,
-- or a String, for example.

class HTML a where
      toHtml     :: a -> Html
      toHtmlFromList :: [a] -> Html

      toHtmlFromList xs = Html (concat [ x | (Html x) <- map toHtml xs])

instance HTML Html where
      toHtml a    = a

instance HTML Char where
      toHtml       a = toHtml [a]
      toHtmlFromList []  = Html []
      toHtmlFromList str = Html [HtmlString (stringToHtmlString str)]

instance (HTML a) => HTML [a] where
      toHtml xs = toHtmlFromList xs

class ADDATTRS a where
      (!) :: a -> [HtmlAttr] -> a

instance (ADDATTRS b) => ADDATTRS (a -> b) where
      fn ! attr = \ arg -> fn arg ! attr

instance ADDATTRS Html where
      (Html htmls) ! attr = Html (map addAttrs htmls)
        where
              addAttrs (html@(HtmlTag { markupAttrs = markupAttrs }) )
                              = html { markupAttrs = markupAttrs ++ attr }
              addAttrs html = html


nest            :: (HTML a) => (Html -> b) -> a        -> b
fn `nest` arg = fn (toHtml arg)


-- concatHtml :: (HTML a) => [a] -> Html
-- concatHtml as = Html (concat (map (getHtmlElements . toHtml) as))

combine :: (HTML a, HTML b) => a -> b -> Html
a `combine` b = Html (getHtmlElements (toHtml a) ++ getHtmlElements (toHtml b))

noHtml :: Html
noHtml = Html []


isNoHtml (Html xs) = null xs


tag  :: String -> Html -> Html
tag str       htmls = Html [
      HtmlTag {
              markupTag = str,
              markupAttrs = [],
              markupContent = htmls }]

itag :: String -> Html
itag str = tag str noHtml

emptyAttr :: String -> HtmlAttr
emptyAttr s = HtmlAttr s ""

intAttr :: String -> Int -> HtmlAttr
intAttr s i = HtmlAttr s (show i)

strAttr :: String -> String -> HtmlAttr
strAttr s t = HtmlAttr s t


{-
foldHtml :: (String -> [HtmlAttr] -> [a] -> a)
      -> (String -> a)
      -> Html
      -> a
foldHtml f g (HtmlTag str attr fmls)
      = f str attr (map (foldHtml f g) fmls)
foldHtml f g (HtmlString  str)
      = g str

-}
-- Processing Strings into Html friendly things.
-- This converts a String to a Html String.
stringToHtmlString :: String -> String
stringToHtmlString = concatMap fixChar
    where
      fixChar '<' = "&lt;"
      fixChar '>' = "&gt;"
      fixChar '&' = "&amp;"
      fixChar '"' = "&quot;"
      fixChar  c  = [c]

-- ---------------------------------------------------------------------------
-- Classes

instance Show Html where
      showsPrec _ html = showString (prettyHtml html)
      showList htmls   = showString (concat (map show htmls))

instance Show HtmlAttr where
      showsPrec _ (HtmlAttr str val) =
              showString str .
              showString "=" .
              shows val


-- ---------------------------------------------------------------------------
-- Data types

type URL = String

-- ---------------------------------------------------------------------------
-- Basic primitives

-- This is not processed for special chars.
-- use stringToHtml or lineToHtml instead, for user strings,
-- because they  understand special chars, like '<'.

primHtml      :: String                                -> Html
primHtml x    = Html [HtmlString x]

-- ---------------------------------------------------------------------------
-- Basic Combinators

stringToHtml          :: String                       -> Html
stringToHtml = primHtml . stringToHtmlString

-- This converts a string, but keeps spaces as non-line-breakable

lineToHtml            :: String                       -> Html
lineToHtml = primHtml . concatMap htmlizeChar2 . stringToHtmlString
   where
      htmlizeChar2 ' ' = "&nbsp;"
      htmlizeChar2 c   = [c]

-- ---------------------------------------------------------------------------
-- Html Constructors

-- (automatically generated)


address             :: Html -> Html
address             =  tag "ADDRESS"
anchor              :: Html -> Html
anchor              =  tag "A"
applet              :: Html -> Html
applet              =  tag "APPLET"
area                ::         Html
area                = itag "AREA"
basefont            ::         Html
basefont            = itag "BASEFONT"
big                 :: Html -> Html
big                 =  tag "BIG"
blockquote          :: Html -> Html
blockquote          =  tag "BLOCKQUOTE"
body                :: Html -> Html
body                =  tag "BODY"
bold                :: Html -> Html
bold                =  tag "B"
br                  ::         Html
br                  = itag "BR"
caption             :: Html -> Html
caption             =  tag "CAPTION"
center              :: Html -> Html
center              =  tag "CENTER"
cite                :: Html -> Html
cite                =  tag "CITE"
ddef                :: Html -> Html
ddef                =  tag "DD"
define              :: Html -> Html
define              =  tag "DFN"
dlist               :: Html -> Html
dlist               =  tag "DL"
dterm               :: Html -> Html
dterm               =  tag "DT"
emphasize           :: Html -> Html
emphasize           =  tag "EM"
fieldset            :: Html -> Html
fieldset            =  tag "FIELDSET"
font                :: Html -> Html
font                =  tag "FONT"
form                :: Html -> Html
form                =  tag "FORM"
frame               :: Html -> Html
frame               =  tag "FRAME"
frameset            :: Html -> Html
frameset            =  tag "FRAMESET"
h1                  :: Html -> Html
h1                  =  tag "H1"
h2                  :: Html -> Html
h2                  =  tag "H2"
h3                  :: Html -> Html
h3                  =  tag "H3"
h4                  :: Html -> Html
h4                  =  tag "H4"
h5                  :: Html -> Html
h5                  =  tag "H5"
h6                  :: Html -> Html
h6                  =  tag "H6"
header              :: Html -> Html
header              =  tag "HEAD"
hr                  ::         Html
hr                  = itag "HR"
image               ::         Html
image               = itag "IMG"
input               ::         Html
input               = itag "INPUT"
italics             :: Html -> Html
italics             =  tag "I"
keyboard            :: Html -> Html
keyboard            =  tag "KBD"
legend              :: Html -> Html
legend              =  tag "LEGEND"
li                  :: Html -> Html
li                  =  tag "LI"
meta                ::         Html
meta                = itag "META"
noframes            :: Html -> Html
noframes            =  tag "NOFRAMES"
olist               :: Html -> Html
olist               =  tag "OL"
option              :: Html -> Html
option              =  tag "OPTION"
paragraph           :: Html -> Html
paragraph           =  tag "P"
param               ::         Html
param               = itag "PARAM"
pre                 :: Html -> Html
pre                 =  tag "PRE"
samp                :: Html -> Html
samp                =  tag "SAMP"
select              :: Html -> Html
select              =  tag "SELECT"
small               :: Html -> Html
small               =  tag "SMALL"
strong              :: Html -> Html
strong              =  tag "STRONG"
style               :: Html -> Html
style               =  tag "STYLE"
sub                 :: Html -> Html
sub                 =  tag "SUB"
sup                 :: Html -> Html
sup                 =  tag "SUP"
table               :: Html -> Html
table               =  tag "TABLE"
td                  :: Html -> Html
td                  =  tag "TD"
textarea            :: Html -> Html
textarea            =  tag "TEXTAREA"
th                  :: Html -> Html
th                  =  tag "TH"
thebase             ::         Html
thebase             = itag "BASE"
thecode             :: Html -> Html
thecode             =  tag "CODE"
thediv              :: Html -> Html
thediv              =  tag "DIV"
thehtml             :: Html -> Html
thehtml             =  tag "HTML"
thelink             :: Html -> Html
thelink             =  tag "LINK"
themap              :: Html -> Html
themap              =  tag "MAP"
thespan             :: Html -> Html
thespan             =  tag "SPAN"
thetitle            :: Html -> Html
thetitle            =  tag "TITLE"
tr                  :: Html -> Html
tr                  =  tag "TR"
tt                  :: Html -> Html
tt                  =  tag "TT"
ulist               :: Html -> Html
ulist               =  tag "UL"
underline           :: Html -> Html
underline           =  tag "U"
variable            :: Html -> Html
variable            =  tag "VAR"

-- ---------------------------------------------------------------------------
-- Html Attributes

-- (automatically generated)

action              :: String -> HtmlAttr
align               :: String -> HtmlAttr
alink               :: String -> HtmlAttr
alt                 :: String -> HtmlAttr
altcode             :: String -> HtmlAttr
archive             :: String -> HtmlAttr
background          :: String -> HtmlAttr
base                :: String -> HtmlAttr
bgcolor             :: String -> HtmlAttr
border              :: Int    -> HtmlAttr
bordercolor         :: String -> HtmlAttr
cellpadding         :: Int    -> HtmlAttr
cellspacing         :: Int    -> HtmlAttr
clear               :: String -> HtmlAttr
code                :: String -> HtmlAttr
codebase            :: String -> HtmlAttr
color               :: String -> HtmlAttr
cols                :: String -> HtmlAttr
colspan             :: Int    -> HtmlAttr
content             :: String -> HtmlAttr
coords              :: String -> HtmlAttr
enctype             :: String -> HtmlAttr
face                :: String -> HtmlAttr
frameborder         :: Int    -> HtmlAttr
height              :: Int    -> HtmlAttr
href                :: String -> HtmlAttr
hspace              :: Int    -> HtmlAttr
httpequiv           :: String -> HtmlAttr
identifier          :: String -> HtmlAttr
lang                :: String -> HtmlAttr
link                :: String -> HtmlAttr
marginheight        :: Int    -> HtmlAttr
marginwidth         :: Int    -> HtmlAttr
maxlength           :: Int    -> HtmlAttr
method              :: String -> HtmlAttr
name                :: String -> HtmlAttr
rel                 :: String -> HtmlAttr
rev                 :: String -> HtmlAttr
rows                :: String -> HtmlAttr
rowspan             :: Int    -> HtmlAttr
rules               :: String -> HtmlAttr
scrolling           :: String -> HtmlAttr
shape               :: String -> HtmlAttr
size                :: String -> HtmlAttr
src                 :: String -> HtmlAttr
start               :: Int    -> HtmlAttr
target              :: String -> HtmlAttr
text                :: String -> HtmlAttr
theclass            :: String -> HtmlAttr
thestyle            :: String -> HtmlAttr
thetype             :: String -> HtmlAttr
title               :: String -> HtmlAttr
usemap              :: String -> HtmlAttr
valign              :: String -> HtmlAttr
value               :: String -> HtmlAttr
version             :: String -> HtmlAttr
vlink               :: String -> HtmlAttr
vspace              :: Int    -> HtmlAttr
width               :: String -> HtmlAttr

checked             ::           HtmlAttr
compact             ::           HtmlAttr
ismap               ::           HtmlAttr
multiple            ::           HtmlAttr
selected            ::           HtmlAttr

action              =   strAttr "ACTION"
align               =   strAttr "ALIGN"
alink               =   strAttr "ALINK"
alt                 =   strAttr "ALT"
altcode             =   strAttr "ALTCODE"
archive             =   strAttr "ARCHIVE"
background          =   strAttr "BACKGROUND"
base                =   strAttr "BASE"
bgcolor             =   strAttr "BGCOLOR"
border              =   intAttr "BORDER"
bordercolor         =   strAttr "BORDERCOLOR"
cellpadding         =   intAttr "CELLPADDING"
cellspacing         =   intAttr "CELLSPACING"
checked             = emptyAttr "CHECKED"
clear               =   strAttr "CLEAR"
code                =   strAttr "CODE"
codebase            =   strAttr "CODEBASE"
color               =   strAttr "COLOR"
cols                =   strAttr "COLS"
colspan             =   intAttr "COLSPAN"
compact             = emptyAttr "COMPACT"
content             =   strAttr "CONTENT"
coords              =   strAttr "COORDS"
enctype             =   strAttr "ENCTYPE"
face                =   strAttr "FACE"
frameborder         =   intAttr "FRAMEBORDER"
height              =   intAttr "HEIGHT"
href                =   strAttr "HREF"
hspace              =   intAttr "HSPACE"
httpequiv           =   strAttr "HTTP-EQUIV"
identifier          =   strAttr "ID"
ismap               = emptyAttr "ISMAP"
lang                =   strAttr "LANG"
link                =   strAttr "LINK"
marginheight        =   intAttr "MARGINHEIGHT"
marginwidth         =   intAttr "MARGINWIDTH"
maxlength           =   intAttr "MAXLENGTH"
method              =   strAttr "METHOD"
multiple            = emptyAttr "MULTIPLE"
name                =   strAttr "NAME"
nohref              = emptyAttr "NOHREF"
noresize            = emptyAttr "NORESIZE"
noshade             = emptyAttr "NOSHADE"
nowrap              = emptyAttr "NOWRAP"
rel                 =   strAttr "REL"
rev                 =   strAttr "REV"
rows                =   strAttr "ROWS"
rowspan             =   intAttr "ROWSPAN"
rules               =   strAttr "RULES"
scrolling           =   strAttr "SCROLLING"
selected            = emptyAttr "SELECTED"
shape               =   strAttr "SHAPE"
size                =   strAttr "SIZE"
src                 =   strAttr "SRC"
start               =   intAttr "START"
target              =   strAttr "TARGET"
text                =   strAttr "TEXT"
theclass            =   strAttr "CLASS"
thestyle            =   strAttr "STYLE"
thetype             =   strAttr "TYPE"
title               =   strAttr "TITLE"
usemap              =   strAttr "USEMAP"
valign              =   strAttr "VALIGN"
value               =   strAttr "VALUE"
version             =   strAttr "VERSION"
vlink               =   strAttr "VLINK"
vspace              =   intAttr "VSPACE"
width               =   strAttr "WIDTH"

-- ---------------------------------------------------------------------------
-- Html Constructors

-- (automatically generated)

validHtmlTags :: [String]
validHtmlTags = [
      "ADDRESS",
      "A",
      "APPLET",
      "BIG",
      "BLOCKQUOTE",
      "BODY",
      "B",
      "CAPTION",
      "CENTER",
      "CITE",
      "DD",
      "DFN",
      "DL",
      "DT",
      "EM",
      "FIELDSET",
      "FONT",
      "FORM",
      "FRAME",
      "FRAMESET",
      "H1",
      "H2",
      "H3",
      "H4",
      "H5",
      "H6",
      "HEAD",
      "I",
      "KBD",
      "LEGEND",
      "LI",
      "NOFRAMES",
      "OL",
      "OPTION",
      "P",
      "PRE",
      "SAMP",
      "SELECT",
      "SMALL",
      "STRONG",
      "STYLE",
      "SUB",
      "SUP",
      "TABLE",
      "TD",
      "TEXTAREA",
      "TH",
      "CODE",
      "DIV",
      "HTML",
      "LINK",
      "MAP",
      "TITLE",
      "TR",
      "TT",
      "UL",
      "U",
      "VAR"]

validHtmlITags :: [String]
validHtmlITags = [
      "AREA",
      "BASEFONT",
      "BR",
      "HR",
      "IMG",
      "INPUT",
      "META",
      "PARAM",
      "BASE"]

validHtmlAttrs :: [String]
validHtmlAttrs = [
      "ACTION",
      "ALIGN",
      "ALINK",
      "ALT",
      "ALTCODE",
      "ARCHIVE",
      "BACKGROUND",
      "BASE",
      "BGCOLOR",
      "BORDER",
      "BORDERCOLOR",
      "CELLPADDING",
      "CELLSPACING",
      "CHECKED",
      "CLEAR",
      "CODE",
      "CODEBASE",
      "COLOR",
      "COLS",
      "COLSPAN",
      "COMPACT",
      "CONTENT",
      "COORDS",
      "ENCTYPE",
      "FACE",
      "FRAMEBORDER",
      "HEIGHT",
      "HREF",
      "HSPACE",
      "HTTP-EQUIV",
      "ID",
      "ISMAP",
      "LANG",
      "LINK",
      "MARGINHEIGHT",
      "MARGINWIDTH",
      "MAXLENGTH",
      "METHOD",
      "MULTIPLE",
      "NAME",
      "NOHREF",
      "NORESIZE",
      "NOSHADE",
      "NOWRAP",
      "REL",
      "REV",
      "ROWS",
      "ROWSPAN",
      "RULES",
      "SCROLLING",
      "SELECTED",
      "SHAPE",
      "SIZE",
      "SRC",
      "START",
      "TARGET",
      "TEXT",
      "CLASS",
      "STYLE",
      "TYPE",
      "TITLE",
      "USEMAP",
      "VALIGN",
      "VALUE",
      "VERSION",
      "VLINK",
      "VSPACE",
      "WIDTH"]

-- ---------------------------------------------------------------------------
-- Html colors

aqua          :: String
black         :: String
blue          :: String
fuchsia       :: String
gray          :: String
green         :: String
lime          :: String
maroon        :: String
navy          :: String
olive         :: String
purple        :: String
red           :: String
silver        :: String
teal          :: String
yellow        :: String
white         :: String

aqua          = "aqua"
black         = "black"
blue          = "blue"
fuchsia       = "fuchsia"
gray          = "gray"
green         = "green"
lime          = "lime"
maroon        = "maroon"
navy          = "navy"
olive         = "olive"
purple        = "purple"
red           = "red"
silver        = "silver"
teal          = "teal"
yellow        = "yellow"
white         = "white"

-- ---------------------------------------------------------------------------
-- Basic Combinators

linesToHtml :: [String]       -> Html

linesToHtml []     = noHtml
linesToHtml (x:[]) = lineToHtml x
linesToHtml (x:xs) = lineToHtml x `combine` br `combine` linesToHtml xs


-- ---------------------------------------------------------------------------
-- Html abbriviations

primHtmlChar  :: String -> Html
copyright     :: Html
spaceHtml     :: Html
bullet        :: Html
p             :: Html -> Html

primHtmlChar  = \ x -> primHtml ("&" ++ x ++ ";")
copyright     = primHtmlChar "copy"
spaceHtml     = primHtmlChar "nbsp"
bullet        = primHtmlChar "#149"

p             = paragraph

-- ---------------------------------------------------------------------------
-- Html tables

class HTMLTABLE ht where
      cell :: ht -> HtmlTable

instance HTMLTABLE HtmlTable where
      cell = id

instance HTMLTABLE Html where
      cell h =
         let
              cellFn x y = h ! (add x colspan $ add y rowspan $ [])
              add 1 fn rest = rest
              add n fn rest = fn n : rest
              r = BT.single cellFn
         in
              mkHtmlTable r

-- We internally represent the Cell inside a Table with an
-- object of the type
-- \pre{
-- 	   Int -> Int -> Html
-- }
-- When we render it later, we find out how many columns
-- or rows this cell will span over, and can
-- include the correct colspan/rowspan command.

newtype HtmlTable
      = HtmlTable (BT.BlockTable (Int -> Int -> Html))


above,beside :: (HTMLTABLE ht1,HTMLTABLE ht2)
                       => ht1 -> ht2 -> HtmlTable
aboves,besides                 :: (HTMLTABLE ht) => [ht] -> HtmlTable
simpleTable            :: [HtmlAttr] -> [HtmlAttr] -> [[Html]] -> Html


mkHtmlTable :: BT.BlockTable (Int -> Int -> Html) -> HtmlTable
mkHtmlTable r = HtmlTable r

-- We give both infix and nonfix, take your pick.
-- Notice that there is no concept of a row/column
-- of zero items.

above   a b = combineFn BT.above (cell a) (cell b)
beside  a b = combineFn BT.beside (cell a) (cell b)


combineFn fn (HtmlTable a) (HtmlTable b) = mkHtmlTable (a `fn` b)

-- Both aboves and besides presume a non-empty list.
-- here is no concept of a empty row or column in these
-- table combinators.

aboves []  = error "aboves []"
aboves xs  = foldr1 (above) (map cell xs)
besides [] = error "besides []"
besides xs = foldr1 (beside) (map cell xs)

-- renderTable takes the HtmlTable, and renders it back into
-- and Html object.

renderTable :: BT.BlockTable (Int -> Int -> Html) -> Html
renderTable theTable
      = concatHtml
          [tr `nest` [theCell x y | (theCell,(x,y)) <- theRow ]
                      | theRow <- BT.getMatrix theTable]
      where
        concatHtml :: (HTML a) => [a] -> Html
        concatHtml as = Html (concat (map (getHtmlElements . toHtml) as))

instance HTML HtmlTable where
      toHtml (HtmlTable tab) = renderTable tab

instance Show HtmlTable where
      showsPrec _ (HtmlTable tab) = shows (renderTable tab)


-- If you can't be bothered with the above, then you
-- can build simple tables with simpleTable.
-- Just provide the attributes for the whole table,
-- attributes for the cells (same for every cell),
-- and a list of lists of cell contents,
-- and this function will build the table for you.
-- It does presume that all the lists are non-empty,
-- and there is at least one list.
--
-- Different length lists means that the last cell
-- gets padded. If you want more power, then
-- use the system above, or build tables explicitly.

simpleTable attr cellAttr lst
      = table ! attr
          `nest`  (aboves
              . map (besides . map ((td ! cellAttr) . toHtml))
              ) lst


-- ---------------------------------------------------------------------------
-- Tree Displaying Combinators

-- The basic idea is you render your structure in the form
-- of this tree, and then use treeHtml to turn it into a Html
-- object with the structure explicit.

data HtmlTree
      = HtmlLeaf Html
      | HtmlNode Html [HtmlTree] Html
      deriving Show

treeHtml :: [String] -> HtmlTree -> Html
treeHtml colors h = table ! [
                    border 0,
                    cellpadding 0,
                    cellspacing 2] `nest` treeHtml' colors h
     where
      manycolors = scanr (:) []

      treeHtmls :: [[String]] -> [HtmlTree] -> HtmlTable
      treeHtmls c ts = aboves (zipWith treeHtml' c ts)

      treeHtml' :: [String] -> HtmlTree -> HtmlTable
      treeHtml' (c:_) (HtmlLeaf leaf) = cell
                                         (td ! [width "100%"]
                                            `nest` bold
                                               `nest` leaf)
      treeHtml' (c:cs@(c2:_)) (HtmlNode hopen ts hclose) =
          if null ts && isNoHtml hclose
          then
              cell hd
          else if null ts
          then
              hd `above` bar `beside` (td ! [bgcolor c2] `nest` spaceHtml)
                 `above` tl
          else
              hd `above` (bar `beside` treeHtmls morecolors ts)
                 `above` tl
        where
              -- This stops a column of colors being the same
              -- color as the immeduately outside nesting bar.
              morecolors = filter ((/= c).head) (manycolors cs)
              bar = td ! [bgcolor c,width "10"] `nest` spaceHtml
              hd = td ! [bgcolor c] `nest` hopen
              tl = td ! [bgcolor c] `nest` hclose
      treeHtml' _ _ = error "The imposible happens"

instance HTML HtmlTree where
      toHtml x = treeHtml treeColors x

-- type "length treeColors" to see how many colors are here.
treeColors = ["#88ccff","#ffffaa","#ffaaff","#ccffff"] ++ treeColors


-- ---------------------------------------------------------------------------
-- Html Debugging Combinators

-- This uses the above tree rendering function, and displays the
-- Html as a tree structure, allowing debugging of what is
-- actually getting produced.

-- debugHtml :: (HTML a) => a -> Html
-- debugHtml obj = table ! [border 0] `nest`
--                   ( th ! [bgcolor "#008888"]
--                      `nest` underline
--                        `nest` "Debugging Output"
--                `above`  td `nest` (toHtml (debug' (toHtml obj)))
--               )
--   where

--       debug' :: Html -> [HtmlTree]
--       debug' (Html markups) = map debug markups

--       debug :: HtmlElement -> HtmlTree
--       debug (HtmlString str) = HtmlLeaf (spaceHtml `combine`
--                                               linesToHtml (lines str))
--       debug (HtmlTag {
--               markupTag = markupTag,
--               markupContent = markupContent,
--               markupAttrs  = markupAttrs
--               }) =
--               case markupContent of
--                 Html [] -> HtmlNode hd [] noHtml
--                 Html xs -> HtmlNode hd (map debug xs) tl
--         where
--               args = if null markupAttrs
--                      then ""
--                      else "  " ++ unwords (map show markupAttrs)
--               hd = font ! [size "1"] `nest` ("<" ++ markupTag ++ args ++ ">")
--               tl = font ! [size "1"] `nest` ("</" ++ markupTag ++ ">")

-- ---------------------------------------------------------------------------
-- Hotlink datatype

data HotLink = HotLink {
      hotLinkURL        :: URL,
      hotLinkContents   :: [Html],
      hotLinkAttributes :: [HtmlAttr]
      } deriving Show

instance HTML HotLink where
      toHtml hl = anchor ! (href (hotLinkURL hl) : hotLinkAttributes hl)
                      `nest` hotLinkContents hl

hotlink :: URL -> [Html] -> HotLink
hotlink url h = HotLink {
      hotLinkURL = url,
      hotLinkContents = h,
      hotLinkAttributes = [] }


-- ---------------------------------------------------------------------------
-- More Combinators

-- (Abridged from Erik Meijer's Original Html library)

-- ordList   :: (HTML a) => [a] -> Html
-- ordList items = olist `nest` map (li `nest`) items

-- unordList :: (HTML a) => [a] -> Html
-- unordList items = ulist `nest` map (li `nest`) items

-- defList   :: (HTML a,HTML b) => [(a,b)] -> Html
-- defList items
--  = dlist `nest` [ [ dterm `nest` bold `nest` dt, ddef `nest` dd ] | (dt,dd) <- items ]


widget :: String -> String -> [HtmlAttr] -> Html
widget w n markupAttrs = input ! ([thetype w,name n] ++ markupAttrs)

checkbox :: String -> String -> Html
hidden   :: String -> String -> Html
radio    :: String -> String -> Html
reset    :: String -> String -> Html
submit   :: String -> String -> Html
password :: String           -> Html
textfield :: String          -> Html
afile    :: String           -> Html
clickmap :: String           -> Html

checkbox n v = widget "CHECKBOX" n [value v]
hidden   n v = widget "HIDDEN"   n [value v]
radio    n v = widget "RADIO"    n [value v]
reset    n v = widget "RESET"    n [value v]
submit   n v = widget "SUBMIT"   n [value v]
password n   = widget "PASSWORD" n []
textfield n  = widget "TEXT"     n []
afile    n   = widget "FILE"     n []
clickmap n   = widget "IMAGE"    n []

menu :: String -> [Html] -> Html
menu n choices
   = select ! [name n] `nest` [ option `nest` p `nest` choice | choice <- choices ]

gui :: String -> Html -> Html
gui act = form ! [action act,method "POST"]

-- ---------------------------------------------------------------------------
-- Html Rendering

-- Uses the append trick to optimize appending.
-- The output is quite messy, because space matters in
-- HTML, so we must not generate needless spaces.

renderHtml :: (HTML html) => html -> String
renderHtml theHtml =
         foldr (.) id (map (renderHtml' 0)
                           (getHtmlElements (tag "HTML" `nest` theHtml))) "\n"

-- Warning: spaces matters in HTML. You are better using renderHtml.
-- This is intentually very inefficent to "encorage" this,
-- but the neater version in easier when debugging.

-- Local Utilities
prettyHtml :: (HTML html) => html -> String
prettyHtml theHtml =
        concat
      $ concat
      $ map prettyHtml'
      $ getHtmlElements
      $ toHtml theHtml

renderHtml' :: Int -> HtmlElement -> ShowS
renderHtml' _ (HtmlString str) = (++) str
renderHtml' n (HtmlTag
              { markupTag = name,
                markupContent = html,
                markupAttrs = markupAttrs })
      = if isNoHtml html && elem name validHtmlITags
        then renderTag True name markupAttrs n
        else (renderTag True name markupAttrs n
             . foldr (.) id (map (renderHtml' (n+2)) (getHtmlElements html))
             . renderTag False name [] n)

prettyHtml' :: HtmlElement -> [String]
prettyHtml' (HtmlString str) = [str]
prettyHtml' (HtmlTag
              { markupTag = name,
                markupContent = html,
                markupAttrs = markupAttrs })
      = if isNoHtml html && elem name validHtmlITags
        then
         [rmNL (renderTag True name markupAttrs 0 "")]
        else
         [rmNL (renderTag True name markupAttrs 0 "")] ++
         (concat (map prettyHtml' (getHtmlElements html))) ++
         [rmNL (renderTag False name [] 0 "")]

rmNL = filter (/= '\n')

-- This prints the Tags The lack of spaces in intentunal, because Html is
-- actually space dependant.

renderTag :: Bool -> String -> [HtmlAttr] -> Int -> ShowS
renderTag x name markupAttrs n r
      = open ++ name ++ rest markupAttrs ++ ">" ++ r
  where
      open = if x then "<" else "</"

      rest []   = ""
      rest attr = unwords (map showPair attr)

      showPair :: HtmlAttr -> String
      showPair (HtmlAttr tag val)
              = tag ++ " = \"" ++ val  ++ "\""

----------------------------------------
-- html size

htmlSize :: Html -> Int
htmlSize (Html xs) = 1 + sum (htmlElementSize <$> xs)

htmlElementSize :: HtmlElement -> Int
htmlElementSize (HtmlString s) = 1
htmlElementSize (HtmlTag _ attrs inner) = 1 + length attrs + htmlSize inner

----------------------------------------
-- Manual generator

genList :: Gen a -> Gen [a]
genList = customListGen 10
  where
    customListGen n gen = do
      n' <- choose (0, n)
      vectorOf n' gen

genHtml :: BoundedGen Html
genHtml d = go d
  where
    go 0 = frequency
      [ (1, Html <$> genList (genHtmlElement 0))
      , (1, pure area)
      , (1, pure basefont)
      , (1, pure br)
      , (1, pure hr)
      , (1, pure image)
      , (1, pure input)
      , (1, pure meta)
      , (1, pure param)
      , (1, pure thebase)
      ]
    go depth = frequency
      [ (1, Html <$> genList (genHtmlElement (depth-1)))
      , (1, pure area)
      , (1, pure basefont)
      , (1, pure br)
      , (1, pure hr)
      , (1, pure image)
      , (1, pure input)
      , (1, pure meta)
      , (1, pure param)
      , (1, pure thebase)
      , (1, address <$> genHtml (depth-1))
      , (1, anchor <$> genHtml (depth-1))
      , (1, applet <$> genHtml (depth-1))
      , (1, big <$> genHtml (depth-1))
      , (1, blockquote <$> genHtml (depth-1))
      , (1, body <$> genHtml (depth-1))
      , (1, bold <$> genHtml (depth-1))
      , (1, caption <$> genHtml (depth-1))
      , (1, center <$> genHtml (depth-1))
      , (1, cite <$> genHtml (depth-1))
      , (1, ddef <$> genHtml (depth-1))
      , (1, define <$> genHtml (depth-1))
      , (1, dlist <$> genHtml (depth-1))
      , (1, dterm <$> genHtml (depth-1))
      , (1, emphasize <$> genHtml (depth-1))
      , (1, fieldset <$> genHtml (depth-1))
      , (1, font <$> genHtml (depth-1))
      , (1, form <$> genHtml (depth-1))
      , (1, frame <$> genHtml (depth-1))
      , (1, frameset <$> genHtml (depth-1))
      , (1, h1 <$> genHtml (depth-1))
      , (1, h2 <$> genHtml (depth-1))
      , (1, h3 <$> genHtml (depth-1))
      , (1, h4 <$> genHtml (depth-1))
      , (1, h5 <$> genHtml (depth-1))
      , (1, h6 <$> genHtml (depth-1))
      , (1, header <$> genHtml (depth-1))
      , (1, italics <$> genHtml (depth-1))
      , (1, keyboard <$> genHtml (depth-1))
      , (1, legend <$> genHtml (depth-1))
      , (1, li <$> genHtml (depth-1))
      , (1, noframes <$> genHtml (depth-1))
      , (1, olist <$> genHtml (depth-1))
      , (1, option <$> genHtml (depth-1))
      , (1, paragraph <$> genHtml (depth-1))
      , (1, pre <$> genHtml (depth-1))
      , (1, samp <$> genHtml (depth-1))
      , (1, select <$> genHtml (depth-1))
      , (1, small <$> genHtml (depth-1))
      , (1, strong <$> genHtml (depth-1))
      , (1, style <$> genHtml (depth-1))
      , (1, sub <$> genHtml (depth-1))
      , (1, sup <$> genHtml (depth-1))
      , (1, table <$> genHtml (depth-1))
      , (1, td <$> genHtml (depth-1))
      , (1, textarea <$> genHtml (depth-1))
      , (1, th <$> genHtml (depth-1))
      , (1, thecode <$> genHtml (depth-1))
      , (1, thediv <$> genHtml (depth-1))
      , (1, thehtml <$> genHtml (depth-1))
      , (1, thelink <$> genHtml (depth-1))
      , (1, themap <$> genHtml (depth-1))
      , (1, thespan <$> genHtml (depth-1))
      , (1, thetitle <$> genHtml (depth-1))
      , (1, tr <$> genHtml (depth-1))
      , (1, tt <$> genHtml (depth-1))
      , (1, ulist <$> genHtml (depth-1))
      , (1, underline <$> genHtml (depth-1))
      , (1, variable <$> genHtml (depth-1))
      ]

genHtmlElement :: BoundedGen HtmlElement
genHtmlElement d = go d
  where
    go 0 = frequency
      [ (1, HtmlString <$> arbitrary)
      ]
    go depth = frequency
      [ (1, HtmlString <$> arbitrary)
      , (1, HtmlTag <$> arbitrary
                    <*> genList (genHtmlAttr (depth-1))
                    <*> genHtml (depth-1))
      ]

genHtmlAttr :: BoundedGen HtmlAttr
genHtmlAttr depth = go depth
  where
    go 0 = frequency
      [ (1, HtmlAttr <$> arbitrary <*> arbitrary)
      , (1, action <$> arbitrary)
      , (1, align <$> arbitrary)
      , (1, alink <$> arbitrary)
      , (1, altcode <$> arbitrary)
      , (1, alt <$> arbitrary)
      , (1, archive <$> arbitrary)
      , (1, background <$> arbitrary)
      , (1, base <$> arbitrary)
      , (1, bgcolor <$> arbitrary)
      , (1, border <$> arbitrary)
      , (1, bordercolor <$> arbitrary)
      , (1, cellpadding <$> arbitrary)
      , (1, cellspacing <$> arbitrary)
      , (1, clear <$> arbitrary)
      , (1, code <$> arbitrary)
      , (1, codebase <$> arbitrary)
      , (1, color <$> arbitrary)
      , (1, cols <$> arbitrary)
      , (1, colspan <$> arbitrary)
      , (1, content <$> arbitrary)
      , (1, coords <$> arbitrary)
      , (1, enctype <$> arbitrary)
      , (1, face <$> arbitrary)
      , (1, frameborder <$> arbitrary)
      , (1, height <$> arbitrary)
      , (1, href <$> arbitrary)
      , (1, hspace <$> arbitrary)
      , (1, httpequiv <$> arbitrary)
      , (1, identifier <$> arbitrary)
      , (1, lang <$> arbitrary)
      , (1, link <$> arbitrary)
      , (1, marginheight <$> arbitrary)
      , (1, marginwidth <$> arbitrary)
      , (1, maxlength <$> arbitrary)
      , (1, method <$> arbitrary)
      , (1, name <$> arbitrary)
      , (1, rel <$> arbitrary)
      , (1, rev <$> arbitrary)
      , (1, rows <$> arbitrary)
      , (1, rowspan <$> arbitrary)
      , (1, rules <$> arbitrary)
      , (1, scrolling <$> arbitrary)
      , (1, shape <$> arbitrary)
      , (1, size <$> arbitrary)
      , (1, src <$> arbitrary)
      , (1, start <$> arbitrary)
      , (1, target <$> arbitrary)
      , (1, text <$> arbitrary)
      , (1, theclass <$> arbitrary)
      , (1, thestyle <$> arbitrary)
      , (1, thetype <$> arbitrary)
      , (1, title <$> arbitrary)
      , (1, usemap <$> arbitrary)
      , (1, valign <$> arbitrary)
      , (1, value <$> arbitrary)
      , (1, version <$> arbitrary)
      , (1, vlink <$> arbitrary)
      , (1, vspace <$> arbitrary)
      , (1, width <$> arbitrary)
      , (1, pure checked)
      , (1, pure compact)
      , (1, pure ismap)
      , (1, pure multiple)
      , (1, pure selected)
      ]
    go _ = frequency
      [ (1, HtmlAttr <$> arbitrary <*> arbitrary)
      , (1, action <$> arbitrary)
      , (1, align <$> arbitrary)
      , (1, alink <$> arbitrary)
      , (1, altcode <$> arbitrary)
      , (1, alt <$> arbitrary)
      , (1, archive <$> arbitrary)
      , (1, background <$> arbitrary)
      , (1, base <$> arbitrary)
      , (1, bgcolor <$> arbitrary)
      , (1, border <$> arbitrary)
      , (1, bordercolor <$> arbitrary)
      , (1, cellpadding <$> arbitrary)
      , (1, cellspacing <$> arbitrary)
      , (1, clear <$> arbitrary)
      , (1, code <$> arbitrary)
      , (1, codebase <$> arbitrary)
      , (1, color <$> arbitrary)
      , (1, cols <$> arbitrary)
      , (1, colspan <$> arbitrary)
      , (1, content <$> arbitrary)
      , (1, coords <$> arbitrary)
      , (1, enctype <$> arbitrary)
      , (1, face <$> arbitrary)
      , (1, frameborder <$> arbitrary)
      , (1, height <$> arbitrary)
      , (1, href <$> arbitrary)
      , (1, hspace <$> arbitrary)
      , (1, httpequiv <$> arbitrary)
      , (1, identifier <$> arbitrary)
      , (1, lang <$> arbitrary)
      , (1, link <$> arbitrary)
      , (1, marginheight <$> arbitrary)
      , (1, marginwidth <$> arbitrary)
      , (1, maxlength <$> arbitrary)
      , (1, method <$> arbitrary)
      , (1, name <$> arbitrary)
      , (1, rel <$> arbitrary)
      , (1, rev <$> arbitrary)
      , (1, rows <$> arbitrary)
      , (1, rowspan <$> arbitrary)
      , (1, rules <$> arbitrary)
      , (1, scrolling <$> arbitrary)
      , (1, shape <$> arbitrary)
      , (1, size <$> arbitrary)
      , (1, src <$> arbitrary)
      , (1, start <$> arbitrary)
      , (1, target <$> arbitrary)
      , (1, text <$> arbitrary)
      , (1, theclass <$> arbitrary)
      , (1, thestyle <$> arbitrary)
      , (1, thetype <$> arbitrary)
      , (1, title <$> arbitrary)
      , (1, usemap <$> arbitrary)
      , (1, valign <$> arbitrary)
      , (1, value <$> arbitrary)
      , (1, version <$> arbitrary)
      , (1, vlink <$> arbitrary)
      , (1, vspace <$> arbitrary)
      , (1, width <$> arbitrary)
      , (1, pure checked)
      , (1, pure compact)
      , (1, pure ismap)
      , (1, pure multiple)
      , (1, pure selected)
      ]


----------------------------------------
-- Dragen2

derive
  [''Html, ''HtmlElement, ''HtmlAttr]
  [ constructors ''Html
  , interface    ''Html |> blacklist ['combine, 'renderTable, 'treeHtml]
  , constructors ''HtmlElement
  , constructors ''HtmlAttr
  , interface    ''HtmlAttr
  ]

type Html_S =
  '[ "Html"
       := Con "Html"
       :+ Fun "area"
       :+ Fun "basefont"
       :+ Fun "br"
       :+ Fun "hr"
       :+ Fun "image"
       :+ Fun "input"
       :+ Fun "meta"
       :+ Fun "param"
       :+ Fun "thebase"
       :+ Fun "address"
       :+ Fun "anchor"
       :+ Fun "applet"
       :+ Fun "big"
       :+ Fun "blockquote"
       :+ Fun "body"
       :+ Fun "bold"
       :+ Fun "caption"
       :+ Fun "center"
       :+ Fun "cite"
       :+ Fun "ddef"
       :+ Fun "define"
       :+ Fun "dlist"
       :+ Fun "dterm"
       :+ Fun "emphasize"
       :+ Fun "fieldset"
       :+ Fun "font"
       :+ Fun "form"
       :+ Fun "frame"
       :+ Fun "frameset"
       :+ Fun "h1"
       :+ Fun "h2"
       :+ Fun "h3"
       :+ Fun "h4"
       :+ Fun "h5"
       :+ Fun "h6"
       :+ Fun "header"
       :+ Fun "italics"
       :+ Fun "keyboard"
       :+ Fun "legend"
       :+ Fun "li"
       :+ Fun "noframes"
       :+ Fun "olist"
       :+ Fun "option"
       :+ Fun "paragraph"
       :+ Fun "pre"
       :+ Fun "samp"
       :+ Fun "select"
       :+ Fun "small"
       :+ Fun "strong"
       :+ Fun "style"
       :+ Fun "sub"
       :+ Fun "sup"
       :+ Fun "table"
       :+ Fun "td"
       :+ Fun "textarea"
       :+ Fun "th"
       :+ Fun "thecode"
       :+ Fun "thediv"
       :+ Fun "thehtml"
       :+ Fun "thelink"
       :+ Fun "themap"
       :+ Fun "thespan"
       :+ Fun "thetitle"
       :+ Fun "tr"
       :+ Fun "tt"
       :+ Fun "ulist"
       :+ Fun "underline"
       :+ Fun "variable"
   , "HtmlElement"
       := Con "HtmlString"
       :+ Con "HtmlTag"
   , "HtmlAttr"
       := Con "HtmlAttr"
       :+ Fun "action"
       :+ Fun "align"
       :+ Fun "alink"
       :+ Fun "altcode"
       :+ Fun "alt"
       :+ Fun "archive"
       :+ Fun "background"
       :+ Fun "base"
       :+ Fun "bgcolor"
       :+ Fun "border"
       :+ Fun "bordercolor"
       :+ Fun "cellpadding"
       :+ Fun "cellspacing"
       :+ Fun "clear"
       :+ Fun "code"
       :+ Fun "codebase"
       :+ Fun "color"
       :+ Fun "cols"
       :+ Fun "colspan"
       :+ Fun "content"
       :+ Fun "coords"
       :+ Fun "enctype"
       :+ Fun "face"
       :+ Fun "frameborder"
       :+ Fun "height"
       :+ Fun "href"
       :+ Fun "hspace"
       :+ Fun "httpequiv"
       :+ Fun "identifier"
       :+ Fun "lang"
       :+ Fun "link"
       :+ Fun "marginheight"
       :+ Fun "marginwidth"
       :+ Fun "maxlength"
       :+ Fun "method"
       :+ Fun "name"
       :+ Fun "rel"
       :+ Fun "rev"
       :+ Fun "rows"
       :+ Fun "rowspan"
       :+ Fun "rules"
       :+ Fun "scrolling"
       :+ Fun "shape"
       :+ Fun "size"
       :+ Fun "src"
       :+ Fun "start"
       :+ Fun "target"
       :+ Fun "text"
       :+ Fun "theclass"
       :+ Fun "thestyle"
       :+ Fun "thetype"
       :+ Fun "title"
       :+ Fun "usemap"
       :+ Fun "valign"
       :+ Fun "value"
       :+ Fun "version"
       :+ Fun "vlink"
       :+ Fun "vspace"
       :+ Fun "width"
       :+ Fun "checked"
       :+ Fun "compact"
       :+ Fun "ismap"
       :+ Fun "multiple"
       :+ Fun "selected"
   ]

deriveBoundedArbitrary
  [ [] .=> ''Html
  , [] .=> ''HtmlElement
  , [] .=> ''HtmlAttr
  ] ''Html_S

genHtml' :: BoundedGen Html
genHtml' = boundedArbitrary
