"use strict";
// Panel layout: which of the five panels are expanded, and their widths. A minimized panel is a
// rail of `railWidth` pixels; an expanded one is at least `minimumWidth` pixels when space allows.

const Panels = {
  options: { rust: "rust", aeneas: "aeneas", spec: "spec", crypto: "crypto", bridge: "bridge" },
  railWidth: 36,
  minimumWidth: 220,
  // Expanded panels from the URL (`rust=1`, …); Rust and Crypto by default, and never none.
  read(params) {
    const panels = Object.fromEntries(Object.values(this.options).map((key) =>
      [key, params.has(key) ? params.get(key) === "1" : key === "rust" || key === "crypto"]));
    if (!this.count(panels)) panels.rust = true;
    return panels;
  },
  count(state) {
    return Object.values(this.options).filter((key) => state[key]).length;
  },
  active(state) {
    return Object.keys(this.options).filter((key) => state[this.options[key]]);
  },
  // Widths are remembered separately for each combination of expanded panels.
  signature(state) {
    return this.active(state).join(",");
  },
  // Expands or minimizes a panel, keeping at least one expanded; returns whether it changed.
  set(state, option, expanded) {
    if (!Object.values(this.options).includes(option) || state[option] === expanded) return false;
    if (!expanded && this.count(state) === 1) return false;
    state[option] = expanded;
    return true;
  },
  // The relative widths of the expanded panels, summing to 1; equal when `value` is invalid.
  weights(state, value) {
    const active = this.active(state);
    const valid = Array.isArray(value) && value.length === active.length &&
      value.every((weight) => Number.isFinite(weight) && weight > 0) &&
      Number.isFinite(value.reduce((sum, weight) => sum + weight, 0));
    const weights = valid ? value : active.map(() => 1);
    const total = weights.reduce((sum, weight) => sum + weight, 0);
    return weights.map((weight) => weight / total);
  },
  readWeights(state, value) {
    return this.weights(state, typeof value === "string" ? value.split(",").map(Number) : null);
  },
  // Pixel widths of all panels in a container `width` pixels wide.
  layout(state, value, width) {
    const active = this.active(state);
    const weights = this.weights(state, value);
    const available = Math.max(0, (Number.isFinite(width) ? width : 0) -
      (Object.keys(this.options).length - active.length) * this.railWidth);
    const minimum = active.length ? Math.min(this.minimumWidth, available / active.length) : 0;
    const sizes = Object.fromEntries(Object.keys(this.options).map((key) => [key, this.railWidth]));
    let remaining = available;
    let pending = active.map((key, index) => ({ key, weight: weights[index] }));
    // Reserve minimum widths first, then divide the remaining space by weight.
    while (pending.length) {
      const total = pending.reduce((sum, entry) => sum + entry.weight, 0);
      const small = pending.filter((entry) => remaining * entry.weight / total < minimum);
      if (!small.length) {
        for (const entry of pending) sizes[entry.key] = remaining * entry.weight / total;
        break;
      }
      for (const entry of small) sizes[entry.key] = minimum;
      remaining = Math.max(0, remaining - minimum * small.length);
      pending = pending.filter((entry) => !small.includes(entry));
    }
    return { active, sizes, available, minimum };
  },
  // Moves the divider after panel `left` by `delta` pixels, keeping both neighbours at least the
  // minimum width; returns the new weights.
  resize(layout, left, delta) {
    const { active, sizes, available, minimum } = layout;
    const widths = active.map((key) => sizes[key]);
    const index = active.indexOf(left);
    if (index >= 0 && index < active.length - 1 && Number.isFinite(delta)) {
      const movement = Math.max(minimum - widths[index], Math.min(delta, widths[index + 1] - minimum));
      widths[index] += movement;
      widths[index + 1] -= movement;
    }
    return widths.map((width) => available > 0 ? width / available : 1 / active.length);
  },
};
