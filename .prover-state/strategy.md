# Strategy — CI FIX REQUIRED

**The CI build is broken.** This is the top priority. Fix the build errors before doing ANY other work.

## CI errors
```
CI run 24550598954 failed:
2026-04-17T06:10:07.6817313Z error: OpenMath/MultistepMethods.lean:817:28: unexpected token ':'; expected command
```

## Instructions
1. Read the failing files and fix the errors
2. Verify each fix compiles: `lake env lean OpenMath/Foo.lean`
3. Commit and push the fix
4. Only after CI is fixed, proceed with normal strategy
