# CI/CD Quick Start Guide

Get regression tests running on GitHub Actions in 5 minutes.

## Prerequisites

✓ GitHub repository for PdatScorr
✓ Access to PdatDsl and PdatCoreSim repositories

## Setup (Choose One)

### Option A: Public Repositories (Easiest)

1. **Update workflow file** (`.github/workflows/regression-tests.yml`):
   ```yaml
   # Line 20-22: Update repository URLs
   repository: YOUR_USERNAME/PdatDsl
   # Line 27-29: Update repository URLs
   repository: YOUR_USERNAME/PdatCoreSim
   ```

2. **Update README badge**:
   ```markdown
   # Replace YOUR_USERNAME in README.md line 3
   [![Regression Tests](https://github.com/YOUR_USERNAME/PdatScorr/actions/workflows/regression-tests.yml/badge.svg)]...
   ```

3. **Commit and push**:
   ```bash
   git add .github/workflows/regression-tests.yml README.md
   git commit -m "ci: Add GitHub Actions workflow"
   git push
   ```

4. **Done!** Check the **Actions** tab on GitHub.

### Option B: Private Repositories

1. **Create Personal Access Token**:
   - Go to: GitHub → Settings → Developer settings → Personal access tokens
   - Click: **Generate new token (classic)**
   - Select scope: `repo` (Full control of private repositories)
   - Generate and copy the token

2. **Add token to repository secrets**:
   - Go to: PdatScorr repo → Settings → Secrets and variables → Actions
   - Click: **New repository secret**
   - Name: `PAT_TOKEN`
   - Value: Paste your token
   - Click: **Add secret**

3. **Update workflow file**:
   ```yaml
   # Uncomment the "token:" lines (around lines 23, 31)
   - name: Checkout PdatDsl
     uses: actions/checkout@v4
     with:
       repository: YOUR_USERNAME/PdatDsl
       path: PdatDsl
       token: ${{ secrets.PAT_TOKEN }}  # ← Uncomment this

   - name: Checkout PdatCoreSim
     uses: actions/checkout@v4
     with:
       repository: YOUR_USERNAME/PdatCoreSim
       path: PdatCoreSim
       submodules: recursive
       token: ${{ secrets.PAT_TOKEN }}  # ← Uncomment this
   ```

4. **Follow steps 1-3 from Option A** (update URLs, commit, push)

## Verification

1. **Go to Actions tab** in your GitHub repository
2. **Click on the latest workflow run**
3. **Wait ~30 minutes** for first run (builds Synlig & ABC)
4. **See green checkmark** ✅ when tests pass

## What Happens Next

- **Every push** to `main` or `develop` → Tests run automatically
- **Every pull request** → Tests run automatically
- **Subsequent runs** → ~10-15 minutes (uses cached builds)

## Quick Commands

```bash
# Test locally before pushing
cd tests && ./run_regression.sh

# View workflow status
# Go to: https://github.com/YOUR_USERNAME/PdatScorr/actions

# Manual trigger
# Go to: Actions tab → Regression Tests → Run workflow
```

## Troubleshooting

| Issue | Solution |
|-------|----------|
| "Repository not found" | Add PAT_TOKEN (see Option B) |
| "Ibex core not found" | Check PdatCoreSim has submodules |
| Workflow doesn't run | Check Actions are enabled in repo settings |
| Tests fail locally | Run `./tests/run_regression.sh -v` for details |

## Need More Help?

📖 See full documentation: `.github/CICD_SETUP.md`

## Next Steps

- ✅ Tests running on CI
- 📊 Add more tests in `tests/regression/`
- 🔔 Set up Slack/email notifications
- 📈 Add code coverage reporting
