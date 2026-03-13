---
title: "Combining Monoids"
author: Callan McGill
date: "Apr 10, 2024"
tags: [Agda, Haskell, Monoids, Composition]
description: Explorations theca compositional nature of Monoids
quote: "We can encourage modular design by providing a library of standard components together with a conventional interface for connecting the components in flexible ways."
quoteAuthor: Abelson, Sussman
publish: false

---

I recently revisited [this old post](https://www.haskellforall.com/2018/02/the-wizard-monoid.html) on the
"wizard monoid" - the idea being that since `ghc-8.0` we have the following instance:
```haskell
> :i IO
type IO :: * -> *
[...]
instance Monoid a => Monoid (IO a)
```

This means in particular that we can do thing such as:
```
-- Get the files in each directory
getDirs :: [FilePath] -> IO [FilePath]
getDirs = foldMap listDirectory
```

The wizard monoid in the post refers to the type `IO (IO ())` which allows one to describe
such 
