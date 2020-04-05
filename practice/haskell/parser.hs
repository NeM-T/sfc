import Text.Parsec

test11 =      string "ab"  <|> string "ac"
test12 = try (string "ab") <|> string "ac"

main = do
    parseTest test11 "ab"
    parseTest test11 "ac"
    parseTest test12 "ab"
    parseTest test12 "ac"
