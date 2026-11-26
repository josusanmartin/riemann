"""Fetch exactly the Git trees in Sernau's Lake manifest (run from grh-compact)."""
import concurrent.futures, json, pathlib, subprocess
def checkout(pkg):
    dest=pathlib.Path(".lake/packages") / pkg["name"]
    dest.mkdir(parents=True,exist_ok=True)
    def git(*args):
        subprocess.run(["git","-C",str(dest),*args],check=True)
    git("init","-q")
    if not (dest/".git/FETCH_HEAD").is_file():
        subprocess.run(["git","-C",str(dest),"remote","remove","origin"],capture_output=True)
        git("remote","add","origin",pkg["url"])
        git("fetch","--quiet","--depth=1","origin",pkg["rev"])
    git("checkout","--quiet","--detach",pkg["rev"])
    assert subprocess.check_output(["git","-C",str(dest),"rev-parse","HEAD"],text=True).strip()==pkg["rev"]
    print(pkg["name"],pkg["rev"],flush=True)
with concurrent.futures.ThreadPoolExecutor(4) as pool:
    list(pool.map(checkout,json.loads(pathlib.Path("lake-manifest.json").read_text())["packages"]))
