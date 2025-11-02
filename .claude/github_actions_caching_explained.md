# GitHub Actions Timing & Caching Explained

## Timing Breakdown

### First Run (~30 minutes)
```
├── Checkout repos           ~1 min
├── Python setup            ~30 sec
├── Build Synlig            ~15-20 min  ⚠️ SLOW (one-time)
├── Build ABC               ~2-3 min
├── Install pip packages    ~30 sec
└── Run tests              ~10-15 min
    ────────────────────────────────
    TOTAL: ~30 minutes
```

### Subsequent Runs (~10-15 minutes)
```
├── Checkout repos           ~1 min
├── Python setup            ~30 sec (cached)
├── Restore Synlig cache    ~30 sec   ✅ CACHED!
├── Restore ABC cache       ~10 sec   ✅ CACHED!
├── Install pip packages    ~30 sec (cached)
└── Run tests              ~10-15 min
    ────────────────────────────────
    TOTAL: ~10-15 minutes
```

## How Caching Works

### What Gets Cached

1. **Synlig Build** (~500MB)
   - Location: `~/synlig-install`
   - Cache key includes workflow file hash
   - Restores in ~30 seconds vs ~20 minutes to rebuild

2. **ABC Build** (~50MB)
   - Location: `~/abc-install`
   - Cache key is stable
   - Restores in ~10 seconds vs ~3 minutes to rebuild

3. **Python Packages** (~100MB)
   - Handled by `setup-python@v5` action
   - Cache key based on `requirements.txt`
   - Restores automatically

### What Doesn't Get Cached

- **Repository checkouts** - Fast anyway (~1 min)
- **Test execution** - Must run fresh each time

## Cache Behavior

### Cache Lifespan
- Caches persist for **7 days** since last access
- Accessed on every workflow run, so effectively permanent
- Total cache limit: **10GB per repository**

### Cache Invalidation

Caches are invalidated and rebuilt when:

1. **Manual invalidation**:
   ```yaml
   env:
     CACHE_VERSION: v2  # Increment this
   ```

2. **Workflow file changes** (Synlig only):
   - Synlig cache key includes `hashFiles('.github/workflows/regression-tests.yml')`
   - Any edit to workflow → rebuilds Synlig
   - ABC cache is unaffected

3. **requirements.txt changes** (Python packages only):
   - Python package cache auto-detects changes
   - Reinstalls affected packages

4. **Cache expiration**:
   - After 7 days of no access
   - Or when total cache size exceeds 10GB

## Cache Strategy in Our Workflow

```yaml
# Line 45-51: Synlig cache
- name: Cache Synlig
  uses: actions/cache@v4
  with:
    path: ~/synlig-install
    key: ${{ runner.os }}-synlig-v1-${{ hashFiles('...') }}
```

**Key components**:
- `${{ runner.os }}`: Linux/macOS/Windows
- `v1`: Manual version control (CACHE_VERSION)
- `${{ hashFiles(...) }}`: Workflow file hash

```yaml
# Line 78-84: ABC cache
- name: Cache ABC
  uses: actions/cache@v4
  with:
    path: ~/abc-install
    key: ${{ runner.os }}-abc-v1
```

**Simpler key**: No workflow hash, very stable

## Viewing Cache Usage

1. Go to your repository on GitHub
2. Click **Actions** tab
3. Click **Caches** in left sidebar
4. See all active caches with sizes and last access

You should see:
- `Linux-synlig-v1-<hash>` (~500MB)
- `Linux-abc-v1` (~50MB)
- Various Python package caches

## When to Invalidate Caches

### Synlig Issues
If Synlig builds fail or behave strangely:
```yaml
env:
  CACHE_VERSION: v2  # Increment
```

Or wait for it to auto-invalidate on workflow changes.

### ABC Issues
Rare, but if needed:
```yaml
env:
  CACHE_VERSION: v2  # Increment
```

### Python Package Issues
Usually auto-handled. If problems:
```bash
# Remove cache manually via GitHub UI, or
# Update requirements.txt versions
```

## Cost Implications

### GitHub Actions Minutes
- Public repos: **2,000 minutes/month free**
- Private repos: **500 minutes/month free**

### Our Usage
- First run: 30 minutes
- Subsequent: ~12 minutes average
- **~41 runs/month on free tier (private)**
- **~166 runs/month on free tier (public)**

### With vs Without Caching

**Without caching** (every run builds Synlig):
- 30 min × 500 free minutes = ~16 runs/month
- **Very limited!**

**With caching** (our setup):
- 12 min × 500 free minutes = ~41 runs/month
- **Much better!**

## Optimization Tips

### 1. Reduce Test Runs
Only run on specific branches:
```yaml
on:
  push:
    branches: [ main ]  # Only main, not develop
```

### 2. Conditional Execution
Only run on relevant file changes:
```yaml
on:
  push:
    paths:
      - 'scripts/**'
      - 'tests/**'
      - '**.sh'
```

### 3. Parallel Test Execution
Already configured with `pytest-xdist`:
```bash
pytest -n auto  # Use all available cores
```

### 4. Skip Certain Tests
For faster feedback:
```bash
pytest -m "not slow"  # Skip slow tests
```

## Monitoring Cache Effectiveness

Check workflow logs for:
```
Cache restored successfully
Cache Size: ~500 MB (536870912 B)
```

vs

```
Cache not found for input keys: ...
```

## Summary

**Yes, builds are cached!** 🎉

- ✅ First run: ~30 min (builds everything)
- ✅ All subsequent runs: ~10-15 min (restores from cache)
- ✅ Caches persist across runs
- ✅ Automatically managed by GitHub
- ✅ No manual cleanup needed
- ✅ Saves ~18 minutes per run (60% faster!)

The slow build happens **once**, then caches make future runs much faster.
