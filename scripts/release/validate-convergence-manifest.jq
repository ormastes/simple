(.main_to_release.selected_shas | length) ==
  (.main_to_release.selected_shas | unique | length) and
all(.main_to_release.selected_shas[];
    test("^[0-9a-f]{40}$") and ($main_inventory[0] | index(.) != null)) and
(.main_to_release.backports | length) ==
  (.main_to_release.backports | map(.source_commit_sha) | unique | length) and
((.main_to_release.selected_shas | sort) ==
 (.main_to_release.backports | map(.source_commit_sha) | sort)) and
all(.main_to_release.backports[]; . as $backport |
    ($backport.source_commit_sha | test("^[0-9a-f]{40}$")) and
    ($backport.result_commit_sha | test("^[0-9a-f]{40}$")) and
    $backport.target_ref == $release_ref and
    ($main_inventory[0] | index($backport.source_commit_sha) != null) and
    ($release_inventory[0] | index($backport.result_commit_sha) != null)) and
(.release_to_main.classifications | length) ==
  (.release_to_main.classifications | map(.commit_sha) | unique | length) and
all(.release_to_main.classifications[];
    (.commit_sha | test("^[0-9a-f]{40}$")) and
    (.kind == "fix" or .kind == "non_fix") and
    (if .kind == "non_fix" then
       (.reason | type == "string" and test("^[^\\t\\r\\n]{3,256}$")) and
       (.owner | type == "string" and test("^@[A-Za-z0-9][A-Za-z0-9._/-]{0,127}$")) and
       (.expires_at | type == "string" and
        test("^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z$") and
        (fromdateiso8601 > now))
     else
       ((.reason // "") == "" and (.owner // "") == "" and
        (.expires_at // "") == "")
     end))
