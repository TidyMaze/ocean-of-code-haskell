loop a = do
  input <- getLine
  let updated = a + (read input :: Int)
  print updated
  loop updated

main = loop 0