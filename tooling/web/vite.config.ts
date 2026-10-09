/// <reference types="vitest/config" />
import { defineConfig } from "vite";
import react from "@vitejs/plugin-react";
import KumaUI from "@kuma-ui/vite";

export default defineConfig({
  plugins: [react(), KumaUI()],
  server: {
    port: 5173,
    proxy: {
      "/api": "http://127.0.0.1:8788",
    },
  },
  test: {
    environment: "node",
    include: ["src/**/*.test.ts"],
  },
});
