{-# LANGUAGE OverloadedStrings #-}

module Util.EtherescanScraper where

import qualified Data.Text.IO        as T
import           Network.HTTP.Simple (httpSink)
import           Text.HTML.DOM       (sinkDoc)
import           Text.XML.Cursor     (attributeIs, content, element,
                                      fromDocument, ($//), (&/), (&//), (>=>))
import System.Environment
import System.Exit
import Control.Exception.Base
import System.IO
import System.IO.Error
import Network.HTTP.Client
import Data.String.Conversions

main :: IO ()
main = do
    args <- System.Environment.getArgs
    if (length args == 2) then return () else fail "Usage: <smart-contract-address> <output-sol-file>"
    let [address, outFile] = args
    let url = ("https://etherscan.io/address/" ++ (address) ++ "#code")
    req <- parseRequest $ url
    doc <- httpSink req $ const sinkDoc
    --putStrLn "Note that if no solidity code is found then no file will be outputted."
    let cursor = fromDocument doc
        scCode = cursor
                      $// element "pre" >=> (attributeIs "id" "editor")
                      &/ content
    if length scCode == 0 then fail ("No solidity code at " ++ url) else return ()
    let sc = convertString (head scCode)
    writeFile outFile (sc)
     