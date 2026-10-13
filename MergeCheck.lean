import PathMerge.Merge

/-- Standalone finite regression entry point, including mixed five-class predicates;
not imported by the PathMerge library and not a semantic completeness proof. -/
def main : IO UInt32 := PathMerge.runMergeChecks
