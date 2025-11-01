import Lake
open Lake DSL

require Regex from git "https://github.com/pandaman64/lean-regex.git" @ "v4.23.0" / "regex"

package rise_lean where
  -- srcDir := "Rise"
  -- See https://github.com/leanprover/lean4/tree/master/src/lake#github-release-builds
  preferReleaseBuild := true
  releaseRepo?       := none
  buildArchive?      := none

@[default_target]
lean_lib Rise where
  -- This enables the interpreter to run functions marked `@[extern]`.
  precompileModules := true

-- lean_lib Elevate where
--   -- This enables the interpreter to run functions marked `@[extern]`.
--   precompileModules := true

lean_exe rise_lean where
  root := `Main
  supportInterpreter := true

target importTarget pkg : System.FilePath :=
  pkg.afterBuildCacheAsync do
    let oFile := pkg.buildDir / "c" / "ffi.o"
    let srcJob ← inputTextFile <| pkg.dir / "Egg/C" / "ffi.c"
    buildFileAfterDep oFile srcJob fun srcFile => do
      let flags := #["-I", toString (← getLeanIncludeDir), "-fPIC"]
      compileO oFile srcFile flags

extern_lib ffi pkg := do
  let job ← fetch <| pkg.target ``importTarget
  let libFile := pkg.sharedLibDir / nameToStaticLib "ffi"
  buildStaticLib libFile #[job]

extern_lib egg_for_lean pkg := do
  pkg.afterBuildCacheAsync do
    let name      := nameToSharedLib "egg_for_lean"
    let srcPath   := pkg.dir / "Egg" / "Rust" / "target" / "release" / name
    let tgtPath   := pkg.sharedLibDir / name
    let traceFile := pkg.buildDir / "rust" / "egg.trace"
    -- let _ ← buildUnlessUpToDate? traceFile (← getTrace) traceFile do
    let _ ← buildAction (← getTrace) traceFile do
      proc {
        cmd := "cargo",
        args := #["rustc", "--release", "--", "-C", "relocation-model=pic"],
        cwd := pkg.dir / "Egg" / "Rust"
      }
      IO.FS.createDirAll pkg.sharedLibDir
      IO.FS.writeBinFile tgtPath (← IO.FS.readBinFile srcPath)
    return pure tgtPath
