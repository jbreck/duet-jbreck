import choraconfig, os.path

tool = choraconfig.clone_tool("duetcra")
tool["ID"] = "duetrba"
tool["displayname"] = "CRA:rba"
tool["shortname"] = "cra"
tool["cmd"] = [os.path.join(tool["root"],"duet.native"),"-rba","{filename}","-test","{tmpfile}"]
tool["no_assert_line_numbers"] = True
tool["error_callout"] = choraconfig.generic_error_callout

