# Ice Nine - Build automation

set dotenv-load

# List available commands
default:
    @just --list

# Build Lean proofs
lean-build:
    lake build

# Update Lean dependencies
lean-update:
    lake update

# Clean Lean build artifacts
lean-clean:
    lake clean

# Build Rust implementation
rust-build:
    cargo build --release

# Run Rust tests
rust-test:
    cargo test

# Run Rust benchmarks
rust-bench:
    cargo bench

# Format Rust code
rust-fmt:
    cargo fmt

# Lint Rust code
rust-lint:
    cargo clippy -- -D warnings

# Build everything (Lean + Rust)
build: lean-build rust-build

# Test everything
test: rust-test

# Clean everything
clean: lean-clean
    cargo clean

# Check Lean proofs and Rust code
check: lean-build rust-lint rust-test
    @echo "✓ All checks passed"

# Watch Lean files and rebuild on changes
lean-watch:
    while inotifywait -r -e modify lean/; do lake build; done

# Run development environment
dev:
    @echo "Starting development environment..."
    @echo "Run 'just check' to verify everything"

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# Deployment
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# NixOS server configuration (from .env)
server := env_var('DEPLOY_SERVER')
remote-path := env_var('DEPLOY_PATH')

# Sync project to NixOS server
deploy-sync:
    @echo "Syncing to {{server}}:{{remote-path}}..."
    rsync -avz --delete \
        --exclude '.git' \
        --exclude 'target' \
        --exclude '.lake' \
        --exclude 'result' \
        --exclude 'work' \
        ./ {{server}}:{{remote-path}}/
    @echo "✓ Synced to server"

# Build on remote server
deploy-build:
    @echo "Building on {{server}}..."
    ssh {{server}} "cd {{remote-path}} && nix develop --command cargo build --release"
    @echo "✓ Built on server"

# Run tests on remote server
deploy-test:
    @echo "Testing on {{server}}..."
    ssh {{server}} "cd {{remote-path}} && nix develop --command cargo test"

# Full deployment: sync + build
deploy: deploy-sync deploy-build
    @echo "✓ Deployment complete"

# SSH into server at project directory
ssh:
    ssh -t {{server}} "cd {{remote-path}} && nix develop"

# Check server status
deploy-status:
    @echo "Checking {{server}}..."
    ssh {{server}} "cd {{remote-path}} 2>/dev/null && echo '✓ Project exists' || echo '✗ Project not found'"
    ssh {{server}} "which nix && nix --version"
