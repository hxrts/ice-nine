# Ice Nine - Build automation

set dotenv-load

# List available commands
default:
    @just --list

# Download Mathlib pre-built cache (speeds up builds significantly)
lean-cache:
    @echo "Downloading Mathlib cache..."
    lake exe cache get
    @echo "✓ Mathlib cache downloaded"

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
# Documentation
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Build documentation book
book:
    mdbook build

# Serve documentation locally with live reload
serve-book:
    mdbook serve --open

# Clean built documentation
clean-book:
    rm -rf docs/book

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# Deployment (requires DEPLOY_SERVER and DEPLOY_PATH in .env)
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Sync project to NixOS server
deploy-sync:
    @echo "Syncing to $DEPLOY_SERVER:$DEPLOY_PATH..."
    rsync -avz --delete \
        --exclude '.git' \
        --exclude 'target' \
        --exclude '.lake' \
        --exclude 'result' \
        --exclude 'work' \
        ./ $DEPLOY_SERVER:$DEPLOY_PATH/
    @echo "✓ Synced to server"

# Download Mathlib cache on remote server
deploy-cache:
    @echo "Downloading Mathlib cache on $DEPLOY_SERVER..."
    ssh $DEPLOY_SERVER "cd $DEPLOY_PATH && nix develop --command lake exe cache get"
    @echo "✓ Mathlib cache downloaded on server"

# Build Lean on remote server (downloads cache first)
deploy-lean:
    @echo "Building Lean on $DEPLOY_SERVER..."
    ssh $DEPLOY_SERVER "cd $DEPLOY_PATH && nix develop --command bash -c 'lake exe cache get && lake build'"
    @echo "✓ Lean built on server"

# Build Rust on remote server
deploy-build:
    @echo "Building Rust on $DEPLOY_SERVER..."
    ssh $DEPLOY_SERVER "cd $DEPLOY_PATH && nix develop --command cargo build --release"
    @echo "✓ Rust built on server"

# Run tests on remote server
deploy-test:
    @echo "Testing on $DEPLOY_SERVER..."
    ssh $DEPLOY_SERVER "cd $DEPLOY_PATH && nix develop --command cargo test"

# Full deployment: sync + cache + build all
deploy: deploy-sync deploy-lean deploy-build
    @echo "✓ Deployment complete"

# SSH into server at project directory
ssh:
    ssh -t $DEPLOY_SERVER "cd $DEPLOY_PATH && nix develop"

# Check server status
deploy-status:
    @echo "Checking $DEPLOY_SERVER..."
    ssh $DEPLOY_SERVER "cd $DEPLOY_PATH 2>/dev/null && echo '✓ Project exists' || echo '✗ Project not found'"
    ssh $DEPLOY_SERVER "which nix && nix --version"
