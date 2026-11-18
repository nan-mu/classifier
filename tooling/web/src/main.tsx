import { StrictMode } from "react";
import { createRoot } from "react-dom/client";
import { Alive2Page } from "./Alive2Page";
import { App } from "./App";
import "./index.css";

const root = document.getElementById("root");
if (!root) {
  throw new Error("missing #root");
}

const page = window.location.pathname.startsWith("/alive2") ? <Alive2Page /> : <App />;
createRoot(root).render(<StrictMode>{page}</StrictMode>);
