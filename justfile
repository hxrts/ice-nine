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

# Generate docs/SUMMARY.md from markdown files (extracts titles from # headings)
summary:
    #!/usr/bin/env bash
    set -euo pipefail

    docs="docs"
    build_dir="$docs/book"
    out="$docs/SUMMARY.md"

    echo "# Summary" > "$out"
    echo "" >> "$out"

    # Helper function to extract title from markdown file
    get_title() {
        local f="$1"
        local title
        title="$(grep -m1 '^# ' "$f" | sed 's/^# *//')"
        if [ -z "$title" ]; then
            local base="$(basename "${f%.*}")"
            title="$(printf '%s\n' "$base" \
                | tr '._-' '   ' \
                | awk '{for(i=1;i<=NF;i++){ $i=toupper(substr($i,1,1)) substr($i,2) }}1')"
        fi
        echo "$title"
    }

    # Helper function to get chapter name from directory
    get_chapter_name() {
        local dir="$1"
        echo "$dir" | tr '_-' '  ' | awk '{for(i=1;i<=NF;i++){ $i=toupper(substr($i,1,1)) substr($i,2) }}1'
    }

    # Collect all files, organized by directory
    declare -A dirs
    root_files=()

    while IFS= read -r f; do
        rel="${f#$docs/}"

        # Skip SUMMARY.md
        [ "$rel" = "SUMMARY.md" ] && continue

        # Skip files under the build output directory
        case "$f" in "$build_dir"/*) continue ;; esac

        # Check if file is in a subdirectory
        if [[ "$rel" == */* ]]; then
            # Extract directory name (first component of path)
            dir="${rel%%/*}"
            # Add file to this directory's list
            dirs[$dir]+="$f"$'\n'
        else
            # Root-level file
            root_files+=("$f")
        fi
    done < <(find "$docs" -type f -name '*.md' -not -name 'SUMMARY.md' -not -path "$build_dir/*" | LC_ALL=C sort)

    # Write root-level files first
    for f in "${root_files[@]+"${root_files[@]}"}"; do
        rel="${f#$docs/}"
        title="$(get_title "$f")"
        echo "- [$title]($rel)" >> "$out"
    done

    # Write chapters (directories) with their files
    first_chapter=true
    for dir in $(printf '%s\n' "${!dirs[@]}" | LC_ALL=C sort); do
        # Add blank line before chapter (except first if no root files)
        if [ "$first_chapter" = true ]; then
            first_chapter=false
        else
            echo "" >> "$out"
        fi

        # Add chapter heading
        chapter_name="$(get_chapter_name "$dir")"
        echo "# $chapter_name" >> "$out"
        echo "" >> "$out"

        # Add files in this directory
        while IFS= read -r f; do
            [ -z "$f" ] && continue
            rel="${f#$docs/}"
            title="$(get_title "$f")"
            echo "- [$title]($rel)" >> "$out"
        done < <(echo -n "${dirs[$dir]}" | LC_ALL=C sort)
    done

    echo "Generated $out"

# Build documentation book (regenerates SUMMARY.md first)
book: summary
    mdbook-mermaid install . > /dev/null 2>&1 || true
    mdbook build
    rm -f mermaid.min.js mermaid-init.js

# Serve documentation locally with live reload
serve-book: summary
    #!/usr/bin/env bash
    set -euo pipefail

    # Kill any existing mdbook servers
    if pgrep -x mdbook > /dev/null; then
        echo "Stopping existing mdbook server..."
        pkill mdbook
        sleep 1
    fi

    mdbook-mermaid install . > /dev/null 2>&1 || true
    mdbook serve --open

# Clean built documentation
clean-book:
    rm -rf docs/book

# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
# Deployment (requires DEPLOY_SERVER and DEPLOY_PATH in .env)
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

# Clear stale SSH connections (runs before server commands)
# Fixes "No route to host" errors caused by stale ControlMaster sockets
_ssh-reset:
    #!/usr/bin/env bash
    # Extract host from DEPLOY_SERVER (handles user@host format)
    HOST="${DEPLOY_SERVER#*@}"
    # Kill any stale SSH ControlMaster processes for this host
    pkill -f "ssh.*${HOST}.*ControlMaster" 2>/dev/null || true
    # Remove stale control sockets (common locations)
    rm -f ~/.ssh/sockets/*${HOST}* 2>/dev/null || true
    rm -f ~/.ssh/controlmasters/*${HOST}* 2>/dev/null || true
    rm -f /tmp/ssh-*/*${HOST}* 2>/dev/null || true

# Sync project to NixOS server
deploy-sync: _ssh-reset
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
deploy-cache: _ssh-reset
    @echo "Downloading Mathlib cache on $DEPLOY_SERVER..."
    ssh $DEPLOY_SERVER "cd $DEPLOY_PATH && nix develop --accept-flake-config --command lake exe cache get"
    @echo "✓ Mathlib cache downloaded on server"

# Build Lean on remote server (downloads cache first)
# Uses lockfile to prevent concurrent builds
deploy-lean: _ssh-reset
    #!/usr/bin/env bash
    set -euo pipefail
    LOCKFILE="/tmp/ice-nine-build.lock"

    echo "Building Lean on $DEPLOY_SERVER..."

    # Check if a build is already running
    if ssh $DEPLOY_SERVER "test -f $LOCKFILE && ps -p \$(cat $LOCKFILE 2>/dev/null) > /dev/null 2>&1"; then
        echo "✗ Build already in progress (PID: $(ssh $DEPLOY_SERVER "cat $LOCKFILE 2>/dev/null"))"
        echo "  Use 'just deploy-kill' to force-stop the running build"
        exit 1
    fi

    # Acquire lock and build
    ssh $DEPLOY_SERVER "
        echo \$\$ > $LOCKFILE
        trap 'rm -f $LOCKFILE' EXIT
        cd $DEPLOY_PATH && nix develop --accept-flake-config --command bash -c 'lake exe cache get && lake build'
    "
    echo "✓ Lean built on server"

# Force-kill any running build on server
deploy-kill: _ssh-reset
    #!/usr/bin/env bash
    set -euo pipefail
    LOCKFILE="/tmp/ice-nine-build.lock"

    echo "Killing builds on $DEPLOY_SERVER..."
    ssh $DEPLOY_SERVER "
        # Kill process from lockfile if it exists
        if [ -f $LOCKFILE ]; then
            pid=\$(cat $LOCKFILE 2>/dev/null)
            if [ -n \"\$pid\" ] && ps -p \$pid > /dev/null 2>&1; then
                echo \"Killing build process \$pid...\"
                kill -9 \$pid 2>/dev/null || true
            fi
            rm -f $LOCKFILE
        fi

        # Kill any stray lake/lean processes
        pkill -9 lake 2>/dev/null || true
        pkill -9 lean 2>/dev/null || true
        sleep 1
        echo 'Remaining processes:'
        pgrep -fl 'lake|lean' || echo '  (none)'
    "
    echo "✓ Builds killed"

# Build Rust on remote server
deploy-build: _ssh-reset
    @echo "Building Rust on $DEPLOY_SERVER..."
    ssh $DEPLOY_SERVER "cd $DEPLOY_PATH && nix develop --accept-flake-config --command cargo build --release"
    @echo "✓ Rust built on server"

# Run tests on remote server
deploy-test: _ssh-reset
    @echo "Testing on $DEPLOY_SERVER..."
    ssh $DEPLOY_SERVER "cd $DEPLOY_PATH && nix develop --accept-flake-config --command cargo test"

# Full deployment: sync + cache + build all
deploy: deploy-sync deploy-lean deploy-build
    @echo "✓ Deployment complete"

# SSH into server at project directory
ssh: _ssh-reset
    ssh -t $DEPLOY_SERVER "cd $DEPLOY_PATH && nix develop --accept-flake-config"

# Check server status
deploy-status: _ssh-reset
    @echo "Checking $DEPLOY_SERVER..."
    ssh $DEPLOY_SERVER "cd $DEPLOY_PATH 2>/dev/null && echo '✓ Project exists' || echo '✗ Project not found'"
    ssh $DEPLOY_SERVER "which nix && nix --version"

# Pin development shell to GC root (prevents garbage collection of dependencies)
# Uses TMPDIR on large volume to avoid filling root during builds
deploy-pin: _ssh-reset
    #!/usr/bin/env bash
    set -euo pipefail
    echo "Pinning development shell on $DEPLOY_SERVER..."
    echo "This may take a while if dependencies need to be built."
    echo ""
    ssh $DEPLOY_SERVER "
        # Set up TMPDIR on large volume (avoids filling root during Rust builds)
        mkdir -p /mnt/data/tmp
        chmod 1777 /mnt/data/tmp
        export TMPDIR=/mnt/data/tmp
        export TEMP=/mnt/data/tmp
        export TMP=/mnt/data/tmp

        # Create GC root directory
        mkdir -p /nix/var/nix/gcroots/per-user/root

        # Build and pin devShell
        cd $DEPLOY_PATH && nix develop \
            --profile /nix/var/nix/gcroots/per-user/root/ice-nine-devshell \
            --accept-flake-config \
            --command true
    "
    echo ""
    echo "✓ Development shell pinned to GC root"

# Free up disk space on server (preserves pinned dependencies)
deploy-gc: _ssh-reset
    #!/usr/bin/env bash
    set -euo pipefail
    echo "Freeing up space on $DEPLOY_SERVER..."
    echo ""
    echo "Before cleanup:"
    ssh $DEPLOY_SERVER "df -h / /nix/store 2>/dev/null || df -h /"
    echo ""
    echo "Running garbage collection (pinned paths will be preserved)..."
    ssh $DEPLOY_SERVER "nix-collect-garbage -d"
    echo ""
    echo "After cleanup:"
    ssh $DEPLOY_SERVER "df -h / /nix/store 2>/dev/null || df -h /"
    echo ""
    echo "✓ Garbage collection complete"

# Show disk usage on server
deploy-df: _ssh-reset
    @echo "Disk usage on $DEPLOY_SERVER:"
    ssh $DEPLOY_SERVER "df -h / /nix/store /mnt/data 2>/dev/null || df -h"

# Show what's pinned (GC roots)
deploy-roots: _ssh-reset
    @echo "GC roots on $DEPLOY_SERVER:"
    ssh $DEPLOY_SERVER "ls -la /nix/var/nix/gcroots/per-user/root/ 2>/dev/null || echo 'No per-user roots'"
    @echo ""
    @echo "Pinned devShell size:"
    ssh $DEPLOY_SERVER "nix path-info -Sh /nix/var/nix/gcroots/per-user/root/ice-nine-devshell 2>/dev/null || echo 'Not pinned yet'"

# Initialize server: sync + pin dependencies (run once, or after flake changes)
deploy-init: deploy-sync deploy-pin deploy-cache-pin
    @echo ""
    @echo "✓ Server initialized with pinned dependencies"
    @echo "  Run 'just deploy-lean' to build Lean proofs"

# Pin Mathlib cache to persistent location (survives rm -rf .lake)
# Moves .lake/packages to /mnt/data/lake-packages and symlinks it back
deploy-cache-pin: _ssh-reset
    #!/usr/bin/env bash
    set -euo pipefail
    echo "Pinning Lake packages cache on $DEPLOY_SERVER..."
    ssh $DEPLOY_SERVER "
        cd $DEPLOY_PATH

        # If .lake/packages exists and is not a symlink, move it to persistent location
        if [ -d .lake/packages ] && [ ! -L .lake/packages ]; then
            echo 'Moving .lake/packages to /mnt/data/lake-packages...'
            rm -rf /mnt/data/lake-packages
            mv .lake/packages /mnt/data/lake-packages
            ln -sf /mnt/data/lake-packages .lake/packages
            echo '✓ Packages moved and symlinked'
        elif [ -L .lake/packages ]; then
            echo '✓ .lake/packages is already a symlink'
        else
            # No packages yet, create the structure
            echo 'Creating persistent packages directory...'
            mkdir -p /mnt/data/lake-packages
            mkdir -p .lake
            ln -sf /mnt/data/lake-packages .lake/packages
            echo '✓ Symlink created'
        fi

        echo ''
        echo 'Cache status:'
        ls -la .lake/ 2>/dev/null || echo '  No .lake directory yet'
        du -sh /mnt/data/lake-packages 2>/dev/null || echo '  No packages cached yet'
    "
    echo ""
    echo "✓ Lake packages pinned to /mnt/data/lake-packages"

# Clean stale IceNine build artifacts (preserves Mathlib cache)
deploy-clean: _ssh-reset
    @echo "Cleaning IceNine build artifacts on $DEPLOY_SERVER..."
    ssh $DEPLOY_SERVER "cd $DEPLOY_PATH && rm -rf .lake/build/lib/lean/IceNine* .lake/build/ir/IceNine* .lake/build/lib/*.olean .lake/build/lib/*.ilean 2>/dev/null || true"
    @echo "✓ IceNine artifacts cleaned (Mathlib cache preserved)"

# Full clean: remove all .lake except packages symlink
deploy-clean-full: _ssh-reset
    #!/usr/bin/env bash
    set -euo pipefail
    echo "Full clean on $DEPLOY_SERVER (preserving packages cache)..."
    ssh $DEPLOY_SERVER "
        cd $DEPLOY_PATH

        # Save symlink target if it exists
        if [ -L .lake/packages ]; then
            target=\$(readlink .lake/packages)
            rm -rf .lake/build .lake/config
            # Recreate structure with symlink
            mkdir -p .lake
            ln -sf \"\$target\" .lake/packages
            echo '✓ Build artifacts removed, packages symlink preserved'
        else
            # No symlink, just clean build directory
            rm -rf .lake/build .lake/config
            echo '✓ Build artifacts removed'
        fi
    "
