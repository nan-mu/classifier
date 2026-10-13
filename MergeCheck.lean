import PathMerge.Merge

/-- Standalone finite regression entry point; not imported by the PathMerge library. -/
def main : IO UInt32 := PathMerge.runMergeChecks
