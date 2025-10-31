# CI/CD Setup Guide

This document explains how to set up and use the GitHub Actions CI/CD pipeline for regression testing.

## Overview

The regression test workflow automatically runs on:
- **Push** to `main` or `develop` branches
- **Pull requests** to `main` or `develop` branches
- **Manual trigger** via GitHub Actions UI

## Workflow File

`.github/workflows/regression-tests.yml`

## What Gets Tested

The workflow runs all regression tests:
- **test_ibex_synthesis.py** - 8 tests for single synthesis runs
- **test_batch_synth.py** - 12 tests for batch parallel synthesis

**Total: 20 tests in ~20 minutes** (including setup time)

## Prerequisites

### Repository Structure

The workflow expects the following repository organization:

```
GitHub Organization/User
├── PdatScorr/          (this repo)
├── PdatDsl/            (DSL parser and codegen)
└── PdatCoreSim/        (contains Ibex core as submodule)
```

### For Private Repositories

If your repos are private, you need to set up a Personal Access Token (PAT):

1. **Create PAT**: GitHub Settings → Developer settings → Personal access tokens → Tokens (classic)
   - Select scopes: `repo` (full control of private repositories)

2. **Add to Secrets**: In PdatScorr repo → Settings → Secrets and variables → Actions
   - Name: `PAT_TOKEN`
   - Value: Your PAT

3. **Update workflow**: Uncomment the `token:` lines in `.github/workflows/regression-tests.yml`

### For Public Repositories

If all repos are public, no additional setup needed! The workflow will work out of the box.

## Setup Steps

### 1. Update Repository URLs

Edit `.github/workflows/regression-tests.yml` and update:

```yaml
# Change YOUR_USERNAME to your actual GitHub username/org
repository: YOUR_USERNAME/PdatDsl
repository: YOUR_USERNAME/PdatCoreSim
```

Also update the badge in `README.md`:

```markdown
[![Regression Tests](https://github.com/YOUR_USERNAME/PdatScorr/actions/workflows/regression-tests.yml/badge.svg)](https://github.com/YOUR_USERNAME/PdatScorr/actions/workflows/regression-tests.yml)
```

### 2. Enable GitHub Actions

1. Go to your repository on GitHub
2. Click **Actions** tab
3. If prompted, click **"I understand my workflows, go ahead and enable them"**

### 3. Commit and Push

```bash
git add .github/workflows/regression-tests.yml
git add README.md
git commit -m "Add GitHub Actions CI/CD for regression tests"
git push
```

### 4. Verify Workflow

1. Go to **Actions** tab in GitHub
2. You should see the workflow running
3. Click on the workflow run to see details

## Workflow Components

### Build Steps

1. **Checkout repositories**
   - PdatScorr (this repo)
   - PdatDsl (dependency)
   - PdatCoreSim (contains Ibex core)

2. **Set up Python 3.10**
   - Caches pip packages for faster builds

3. **Install Synlig** (SystemVerilog frontend)
   - Built from source
   - Cached to avoid rebuilding (~10 min initial build)

4. **Install ABC** (sequential optimization)
   - Built from source
   - Cached to avoid rebuilding (~2 min initial build)

5. **Install Python dependencies**
   - pytest, pytest-xdist, pdat-dsl

6. **Set IBEX_ROOT environment variable**
   - Points to Ibex core in PdatCoreSim

7. **Run regression tests**
   - Uses `./tests/run_regression.sh`
   - 20 minute timeout

8. **Upload artifacts on failure**
   - Saves test outputs for debugging
   - Retained for 7 days

9. **Generate test summary**
   - Shows pass/fail status in GitHub UI

### Caching Strategy

The workflow uses GitHub Actions cache to speed up builds:

- **Synlig cache**: `~/synlig-install` (~500MB)
- **ABC cache**: `~/abc-install` (~50MB)
- **pip cache**: Python packages (~100MB)

**First run**: ~30 minutes (builds everything)
**Subsequent runs**: ~10-15 minutes (uses caches)

To invalidate caches, increment `CACHE_VERSION` in the workflow file.

## Viewing Results

### In GitHub UI

1. Go to **Actions** tab
2. Click on a workflow run
3. Click on the **"Run Regression Tests"** job
4. Expand steps to see detailed output

### Test Summary

After tests complete, a summary appears at the bottom of the job:
- ✅ All Tests Passed
- ❌ Failed Tests (with details)

### Status Badge

The README badge shows the current status:
- ✅ Green: All tests passing
- ❌ Red: Tests failing
- ⚪ Gray: No runs yet

## Manual Triggers

You can manually run the workflow:

1. Go to **Actions** tab
2. Select **"Regression Tests"** workflow
3. Click **"Run workflow"** button
4. Select branch and click **"Run workflow"**

## Debugging Failed Tests

### View Logs

1. Click on the failed workflow run
2. Click on the failed step
3. Expand the output to see error messages

### Download Artifacts

If tests fail, artifacts are uploaded:

1. Scroll to bottom of workflow run page
2. Click **"test-failure-outputs"**
3. Download and extract zip file
4. Contains pytest cache and temp directories

### Common Issues

#### 1. Synlig Build Failure

**Error**: `make install failed`

**Solution**:
- Check Synlig dependencies are installed
- Try invalidating cache (increment `CACHE_VERSION`)
- Check Synlig repo for recent changes

#### 2. Ibex Core Not Found

**Error**: `Ibex core not found at $IBEX_ROOT`

**Solution**:
- Ensure PdatCoreSim is checked out with submodules
- Check `submodules: recursive` in workflow

#### 3. Timeout

**Error**: `The job running on runner ... has exceeded the maximum execution time`

**Solution**:
- Increase `timeout-minutes` in workflow
- Check if a test is hanging (use `-x` flag to stop on first failure)

#### 4. Private Repo Access

**Error**: `Repository not found` or `Permission denied`

**Solution**:
- Add PAT_TOKEN to repository secrets
- Uncomment `token:` lines in workflow
- Ensure PAT has `repo` scope

## Local Testing Before Push

Always test locally before pushing:

```bash
# Run all tests
cd tests
./run_regression.sh

# Run with verbose output
./run_regression.sh -v

# Run specific test file
./run_regression.sh test_batch_synth.py
```

## Workflow Maintenance

### Updating Dependencies

#### Update Python Dependencies

Edit `requirements.txt` and the workflow will automatically install them.

#### Update Synlig

1. Increment `CACHE_VERSION` in workflow
2. Optionally pin to specific Synlig commit:
   ```yaml
   git clone https://github.com/chipsalliance/synlig.git
   cd synlig
   git checkout <commit-hash>
   ```

#### Update ABC

1. Increment `CACHE_VERSION` in workflow
2. Optionally pin to specific ABC commit (similar to Synlig)

### Changing Test Timeout

Edit the workflow file:

```yaml
- name: Run regression tests
  run: |
    cd PdatScorr/tests
    ./run_regression.sh -v
  timeout-minutes: 20  # Adjust this value
```

### Adding More Tests

Just add test files to `tests/regression/` and they'll be automatically picked up by pytest.

## Cost Considerations

GitHub Actions provides:
- **Free tier**: 2,000 minutes/month for public repos
- **Free tier**: 500 minutes/month for private repos (but this can be expanded)

Typical usage:
- Each workflow run: ~15 minutes (after caches warm)
- With caching, cost is minimal

To reduce costs:
- Use caching (already configured)
- Only run on specific branches
- Reduce test parallelism (slower but uses less resources)

## Advanced Configuration

### Matrix Testing

To test on multiple Python versions:

```yaml
strategy:
  matrix:
    python-version: ['3.8', '3.9', '3.10', '3.11']
```

### Conditional Execution

Only run tests on certain file changes:

```yaml
on:
  push:
    paths:
      - 'scripts/**'
      - 'tests/**'
      - '**.sh'
      - 'requirements.txt'
```

### Slack Notifications

Add a step to notify on failure:

```yaml
- name: Slack Notification
  if: failure()
  uses: rtCamp/action-slack-notify@v2
  env:
    SLACK_WEBHOOK: ${{ secrets.SLACK_WEBHOOK }}
```

## Troubleshooting

### Check Workflow Syntax

Use GitHub's workflow validator:
```bash
# Install act (local GitHub Actions runner)
brew install act  # or your package manager

# Test workflow locally
act -l
```

### Enable Debug Logging

Add to workflow:

```yaml
env:
  ACTIONS_STEP_DEBUG: true
  ACTIONS_RUNNER_DEBUG: true
```

## Support

For issues with:
- **Workflow**: Check this document and GitHub Actions docs
- **Tests**: See `tests/regression/README.md`
- **Synlig**: https://github.com/chipsalliance/synlig/issues
- **ABC**: https://github.com/berkeley-abc/abc/issues

## References

- [GitHub Actions Documentation](https://docs.github.com/en/actions)
- [Pytest Documentation](https://docs.pytest.org/)
- [Synlig Repository](https://github.com/chipsalliance/synlig)
- [ABC Repository](https://github.com/berkeley-abc/abc)
