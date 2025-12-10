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
    declare -a root_files

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
    for f in "${root_files[@]}"; do
        rel="${f#$docs/}"
        title="$(get_title "$f")"
        echo "- [$title]($rel)" >> "$out"
    done

    # Write chapters (directories) with their files
    for dir in $(printf '%s\n' "${!dirs[@]}" | LC_ALL=C sort); do
        # Add blank line before chapter
        [ ${#root_files[@]} -gt 0 ] && echo "" >> "$out"

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
    mdbook build

# Serve documentation locally with live reload
serve-book: summary
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
