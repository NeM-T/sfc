import System.Directory
main = do lis <- getDirectoryContents "."
          print lis
