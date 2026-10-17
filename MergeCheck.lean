import Node.Merge

/-- Standalone finite regression entry point, including mixed five-class predicates;
not imported by the Node library and not a semantic completeness proof. -/
def main : IO UInt32 := Node.runMergeChecks
