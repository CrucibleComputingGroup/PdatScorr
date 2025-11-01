# Self-Hosted Runner Setup Guide

The regression tests now run on a self-hosted GitHub Actions runner to avoid Synlig compatibility issues with GitHub's hosted Ubuntu environments.

## Prerequisites

A Linux machine (physical or VM) that:
- Has network access to GitHub
- Can run 24/7 (or at least when you want CI to work)
- Has sufficient resources:
  - **CPU**: 4+ cores recommended
  - **RAM**: 8GB+ recommended
  - **Disk**: 50GB+ free space

## Step 1: Install Dependencies on Runner Machine

On your runner machine, install all required tools:

```bash
# Update system
sudo apt-get update
sudo apt-get upgrade -y

# Install Synlig dependencies and build
sudo apt-get install -y \
  build-essential cmake git \
  tclsh tcl-dev \
  ant default-jre \
  swig \
  python3 python3-dev python3-pip python3-venv \
  uuid uuid-dev \
  flex libfl-dev \
  pkg-config libreadline-dev \
  bison libffi-dev \
  wget

# Install Python package for Surelog
pip3 install orderedmultidict

# Build and install Synlig
cd /tmp
git clone https://github.com/chipsalliance/synlig.git
cd synlig
git submodule sync
git submodule update --init --recursive third_party/{surelog,yosys}
make install -j$(nproc) PREFIX=/usr/local

# Verify Synlig is in PATH
which synlig
synlig --version

# Build and install ABC
cd /tmp
git clone https://github.com/berkeley-abc/abc.git
cd abc
make -j$(nproc)
sudo cp abc /usr/local/bin/

# Verify ABC is in PATH
which abc
abc -q "help"

# Install pytest
pip3 install pytest pytest-xdist

echo "✓ All dependencies installed!"
```

## Step 2: Register Runner with GitHub

### On GitHub:

1. Go to your repository: `https://github.com/CrucibleComputingGroup/PdatScorr`
2. Click **Settings** → **Actions** → **Runners**
3. Click **New self-hosted runner**
4. Select **Linux** as the OS
5. Follow the displayed commands

### On Your Runner Machine:

The GitHub UI will show commands like:

```bash
# Create a folder
mkdir actions-runner && cd actions-runner

# Download the latest runner package
curl -o actions-runner-linux-x64-2.XXX.X.tar.gz -L \
  https://github.com/actions/runner/releases/download/vX.XXX.X/actions-runner-linux-x64-2.XXX.X.tar.gz

# Extract the installer
tar xzf ./actions-runner-linux-x64-2.XXX.X.tar.gz

# Create the runner and start the configuration
./config.sh --url https://github.com/CrucibleComputingGroup/PdatScorr --token YOUR_TOKEN

# Run it!
./run.sh
```

**Important configuration options during `./config.sh`:**
- **Runner name**: Choose a descriptive name (e.g., `synlig-build-server`)
- **Labels**: Keep default `self-hosted,Linux,X64`
- **Work folder**: Use default `_work`

## Step 3: Run as a Service (Recommended)

To keep the runner running permanently:

```bash
# Install as a service
cd ~/actions-runner
sudo ./svc.sh install

# Start the service
sudo ./svc.sh start

# Check status
sudo ./svc.sh status

# View logs
journalctl -u actions.runner.* -f
```

## Step 4: Test the Runner

Push a commit to your repo and watch the Actions tab:

```bash
# Make a trivial change
echo "# Test" >> README.md
git add README.md
git commit -m "test: Trigger self-hosted runner"
git push
```

Go to GitHub Actions tab and you should see:
- The workflow starts
- Shows runner name (your machine)
- Tests execute on your hardware

## Workflow Configuration

The simplified workflow (`regression-tests.yml`) now:
- ✅ Checks out code
- ✅ Installs Python dependencies
- ✅ Runs tests
- ❌ No Synlig/ABC installation (assumes pre-installed)
- ❌ No caching (runner is persistent)

## Security Considerations

### Public Repositories
**WARNING**: Self-hosted runners on public repos can execute arbitrary code from anyone who opens a PR!

**Recommended setup for public repos:**
1. Require approval for workflows from first-time contributors
2. Go to Settings → Actions → General
3. Under "Fork pull request workflows from outside collaborators"
4. Select "Require approval for first-time contributors"

### Private Repositories
Self-hosted runners are safer on private repos since only authorized users can trigger workflows.

## Troubleshooting

### Runner Not Showing Up
- Check runner service status: `sudo ./svc.sh status`
- View logs: `journalctl -u actions.runner.* -f`
- Ensure network connectivity to GitHub

### Tests Failing
- Verify tools are installed: `which synlig abc`
- Check Python packages: `pip3 list | grep pytest`
- Run tests manually: `cd PdatScorr/tests && ./run_regression.sh`

### Runner Offline
- Check service: `sudo ./svc.sh status`
- Restart: `sudo ./svc.sh restart`
- Check disk space: `df -h`

## Maintenance

### Update Dependencies
```bash
# Update Synlig
cd /tmp/synlig
git pull
git submodule update --recursive
make clean
make install -j$(nproc) PREFIX=/usr/local

# Update ABC
cd /tmp/abc
git pull
make clean
make -j$(nproc)
sudo cp abc /usr/local/bin/
```

### Update Runner Software
```bash
cd ~/actions-runner
sudo ./svc.sh stop
./config.sh remove  # Enter your PAT when prompted
# Then re-run setup from Step 2
```

### Remove Runner
```bash
# Stop service
sudo ./svc.sh stop
sudo ./svc.sh uninstall

# Remove from GitHub
# Go to Settings → Actions → Runners → Click ... → Remove
```

## Comparison: Self-Hosted vs GitHub-Hosted

| Feature | GitHub-Hosted | Self-Hosted |
|---------|---------------|-------------|
| Setup | None | One-time setup |
| Cost | Limited free minutes | Free unlimited |
| Speed | Moderate | Fast (no build) |
| Synlig | Build or binary issues | Works (your install) |
| Maintenance | None | Update tools manually |
| Security | Isolated | Need to secure |

## Next Steps

1. **Install dependencies** on your runner machine
2. **Register runner** with GitHub
3. **Start as service** for 24/7 operation
4. **Test** by pushing a commit
5. **Monitor** first few runs

## Resources

- [GitHub Self-Hosted Runners Docs](https://docs.github.com/en/actions/hosting-your-own-runners)
- [Security Hardening](https://docs.github.com/en/actions/security-guides/security-hardening-for-github-actions#hardening-for-self-hosted-runners)
