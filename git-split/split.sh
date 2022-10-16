# How to use split.sh
#
# 1. Run `split.sh bash <id-of-commit-to-split>`
#
# 2. Commit the first part of the split
#
# 3. Run `exit 0`
#
# If you get stuck you can run `exit 1` and the split will be
# cancelled.  You may have to check out your original branch again.
#
# If you have any difficulty using split.sh then file an issue
#
# https://github.com/tomjaguarpaw/ad/issues/new

set -e

# *3      CURRENT
# .  *3   FINISHED
# .  .
# .  .
# *2 .    COMBINED
# |  *2   REST_OF_COMBINED
# |  |
# |  |
# |  *    AFTER_HANDLER
# |  .
# |  .
# |  .
# |  *
# | /
# |/
# |
# |
# *1      COMBINED^

# Empty string if not a symbolic ref
CURRENT_BRANCH=$(git symbolic-ref --quiet --short HEAD || true)
CURRENT=$(git rev-parse HEAD)
CURRENT_SHORT=$(git rev-parse --short HEAD)
if [ -n "$CURRENT_BRANCH" ]; then
    CURRENT_BRANCH_OR_SHORT=$CURRENT_BRANCH
else
    CURRENT_BRANCH_OR_SHORT=$CURRENT_SHORT
fi
COMBINED_PROVIDED=$2
COMBINED=$(git rev-parse $COMBINED_PROVIDED)
COMBINED_SHORT=$(git rev-parse --short $COMBINED_PROVIDED)
HANDLER=$1

# This is the best way I know of to (print an error message and then
# exit) on failure when set -e is set
git merge-base --is-ancestor $COMBINED $CURRENT || (echo "$COMBINED_PROVIDED is not an ancestor of $CURRENT_BRANCH"; false) || exit

COMBINED_PARENT=$(git rev-parse $COMBINED^)
COMBINED_PARENT_SHORT=$(git rev-parse --short $COMBINED^)

echo -n checkout...
git checkout --quiet $COMBINED
echo -n reset...
git reset --quiet $COMBINED_PARENT
echo done

echo "You wanted to split the commit"
echo
git show --no-patch --pretty=short $COMBINED
echo
echo -n "I'm now on $COMBINED_SHORT's parent ($COMBINED_PARENT_SHORT). "
echo "I'm going to drop you into your chosen handler: $HANDLER"
echo -n "Please make exactly one commit and then exit the handler with "
echo "exit code 0."
$HANDLER

AFTER_HANDLER=$(git rev-parse HEAD)
AFTER_HANDLER_SHORT=$(git rev-parse --short HEAD)

echo -n reset...
git reset --quiet --hard $AFTER_HANDLER

echo -n checkout...
git checkout --quiet --force $COMBINED

echo -n reset...
git reset --quiet --soft $AFTER_HANDLER

COMBINED_SUBJECT=$(git diff-tree -s --pretty=%s $COMBINED)
COMBINED_BODY=$(git diff-tree -s --pretty=%b $COMBINED)

echo -n commit...
git commit --allow-empty --quiet -m "$COMBINED_SUBJECT" -m "$COMBINED_BODY"

REST_OF_COMBINED=$(git rev-parse HEAD)
# Check 2 equality
echo -n checking equality...
git diff --exit-code $REST_OF_COMBINED $COMBINED

echo -n rebase...
git rebase --quiet --onto $REST_OF_COMBINED $COMBINED $CURRENT

FINISHED=$(git rev-parse HEAD)
FINISHED_SHORT=$(git rev-parse --short HEAD)
# Check 3 equality
echo -n checking equality...
git diff --exit-code $FINISHED $CURRENT
echo done
echo
echo "Splitting finished successfully!"
echo
echo "You were on $CURRENT_BRANCH_OR_SHORT.  You are now on $FINISHED_SHORT."
echo
echo "You might want to do exactly one of the following"
echo
echo "* An interactive rebase to reword the second split"
echo
echo "  $ git rebase --interactive $AFTER_HANDLER_SHORT $FINISHED_SHORT"

if [ -n "$CURRENT_BRANCH" ]; then
    echo
    echo "* Reset your branch (which doesn't yet contain the split) to this one (which does)"
    echo
    echo "  $ git checkout $CURRENT_BRANCH && git reset --hard $FINISHED_SHORT"
    echo
    echo "* Reset your branch and then rebase to reword"
    echo
    echo "  $ git checkout $CURRENT_BRANCH && git reset --hard $FINISHED_SHORT && git rebase --interactive $AFTER_HANDLER_SHORT"
fi

# Old bits

# AFTER_HANDLER_SUBJECT=$(git diff-tree -s --pretty=%s $AFTER_HANDLER)
# AFTER_HANDLER_BODY=$(git diff-tree -s --pretty=%b $AFTER_HANDLER)
# REST_OF_COMBINED_SUBJECT=$COMBINED_SUBJECT
# REST_OF_COMBINED_BODY="$COMBINED_BODY

# but split, so without:

# $AFTER_HANDLER_SUBJECT

# $AFTER_HANDLER_BODY"
