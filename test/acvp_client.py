#!/usr/bin/env python3
# Copyright (c) The mldsa-native project authors
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

# ACVP client for ML-DSA
#
# Processes 'internalProjection.json' files from
# https://github.com/usnistgov/ACVP-Server/blob/master/gen-val/json-files
#
# Invokes `acvp_mldsa{lvl}` under the hood.

import argparse
import hashlib
import os
import json
import sys
import subprocess
import urllib.request
from pathlib import Path

# Check if we need to use a wrapper for execution (e.g. QEMU)
exec_prefix = os.environ.get("EXEC_WRAPPER", "")
exec_prefix = [exec_prefix] if exec_prefix != "" else []


def download_acvp_files(version="v1.1.0.40"):
    """Download ACVP test files for the specified version if not present."""
    base_url = f"https://raw.githubusercontent.com/usnistgov/ACVP-Server/{version}/gen-val/json-files"

    # Files we need to download for ML-KEM
    files_to_download = [
        "ML-DSA-keyGen-FIPS204/internalProjection.json",
        "ML-DSA-sigGen-FIPS204/internalProjection.json",
        "ML-DSA-sigVer-FIPS204/internalProjection.json",
    ]

    # Create directory structure
    data_dir = Path(f"test/.acvp-data/{version}/files")
    data_dir.mkdir(parents=True, exist_ok=True)

    for file_path in files_to_download:
        local_file = data_dir / file_path
        local_file.parent.mkdir(parents=True, exist_ok=True)

        if not local_file.exists():
            url = f"{base_url}/{file_path}"
            print(f"Downloading {file_path}...", file=sys.stderr)
            try:
                urllib.request.urlretrieve(url, local_file)
                # Verify the file is valid JSON
                with open(local_file, "r") as f:
                    json.load(f)
            except json.JSONDecodeError as e:
                print(
                    f"Error: Downloaded file {file_path} is not valid JSON: {e}",
                    file=sys.stderr,
                )
                local_file.unlink(missing_ok=True)
                return False
            except Exception as e:
                print(f"Error downloading {file_path}: {e}", file=sys.stderr)
                local_file.unlink(missing_ok=True)
                return False

    return True


def loadAcvpData(internalProjection):
    with open(internalProjection, "r") as f:
        internalProjectionData = json.load(f)
    return (internalProjection, internalProjectionData)


def loadDefaultAcvpData(version="v1.1.0.40"):
    data_dir = f"test/.acvp-data/{version}/files"
    acvp_jsons_for_version = [
        f"{data_dir}/ML-DSA-keyGen-FIPS204/internalProjection.json",
        f"{data_dir}/ML-DSA-sigGen-FIPS204/internalProjection.json",
        f"{data_dir}/ML-DSA-sigVer-FIPS204/internalProjection.json",
    ]
    acvp_data = []
    for internalProjection in acvp_jsons_for_version:
        acvp_data.append(loadAcvpData(internalProjection))
    return acvp_data


def err(msg, **kwargs):
    print(msg, file=sys.stderr, **kwargs)


def info(msg, **kwargs):
    print(msg, **kwargs)


def get_acvp_binary(tg):
    """Convert JSON dict for ACVP test group to suitable ACVP binary."""
    parameterSetToLevel = {
        "ML-DSA-44": 44,
        "ML-DSA-65": 65,
        "ML-DSA-87": 87,
    }
    level = parameterSetToLevel[tg["parameterSet"]]
    basedir = f"./test/build/mldsa{level}/bin"
    acvp_bin = f"acvp_mldsa{level}"
    return f"{basedir}/{acvp_bin}"


def run_keyGen_test(tg, tc):
    info(f"Running keyGen test case {tc['tcId']} ... ", end="")
    acvp_bin = get_acvp_binary(tg)
    assert tg["testType"] == "AFT"
    acvp_call = exec_prefix + [
        acvp_bin,
        "keyGen",
        f"seed={tc['seed']}",
    ]
    result = subprocess.run(acvp_call, encoding="utf-8", capture_output=True)
    if result.returncode != 0:
        err("FAIL!")
        err(f"{acvp_call} failed with error code {result.returncode}")
        err(result.stderr)
        exit(1)
    # Extract results and compare to expected data
    for l in result.stdout.splitlines():
        (k, v) = l.split("=")
        if v != tc[k]:
            err("FAIL!")
            err(f"Mismatching result for {k}: expected {tc[k]}, got {v}")
            exit(1)
    info("OK")


def compute_hash(msg, alg):
    msg_bytes = bytes.fromhex(msg)

    if alg == "SHA2-224":
        return hashlib.sha224(msg_bytes).hexdigest()
    elif alg == "SHA2-256":
        return hashlib.sha256(msg_bytes).hexdigest()
    elif alg == "SHA2-384":
        return hashlib.sha384(msg_bytes).hexdigest()
    elif alg == "SHA2-512":
        return hashlib.sha512(msg_bytes).hexdigest()
    elif alg == "SHA2-512/224":
        return hashlib.new("sha512_224", msg_bytes).hexdigest()
    elif alg == "SHA2-512/256":
        return hashlib.new("sha512_256", msg_bytes).hexdigest()
    elif alg == "SHA3-224":
        return hashlib.sha3_224(msg_bytes).hexdigest()
    elif alg == "SHA3-256":
        return hashlib.sha3_256(msg_bytes).hexdigest()
    elif alg == "SHA3-384":
        return hashlib.sha3_384(msg_bytes).hexdigest()
    elif alg == "SHA3-512":
        return hashlib.sha3_512(msg_bytes).hexdigest()
    elif alg == "SHAKE-128":
        return hashlib.shake_128(msg_bytes).hexdigest(32)
    elif alg == "SHAKE-256":
        return hashlib.shake_256(msg_bytes).hexdigest(64)
    else:
        raise ValueError(f"Unsupported hash algorithm: {alg}")


def run_sigGen_test(tg, tc):
    info(f"Running sigGen test case {tc['tcId']} ... ", end="")
    acvp_bin = get_acvp_binary(tg)

    assert tg["testType"] == "AFT"

    # TODO: probably we want to handle handle the deterministic case differently
    if tg["deterministic"] is True:
        tc["rnd"] = "0" * 64

    if tg["preHash"] == "preHash":
        assert len(tc["context"]) <= 2 * 255

        # Use specialized SHAKE256 function that computes hash internally
        if tc["hashAlg"] == "SHAKE-256":
            acvp_call = exec_prefix + [
                acvp_bin,
                "sigGenPreHashShake256",
                f"message={tc['message']}",
                f"context={tc['context']}",
                f"rnd={tc['rnd']}",
                f"sk={tc['sk']}",
            ]
        else:
            ph = compute_hash(tc["message"], tc["hashAlg"])
            acvp_call = exec_prefix + [
                acvp_bin,
                "sigGenPreHash",
                f"ph={ph}",
                f"context={tc['context']}",
                f"rng={tc['rnd']}",
                f"sk={tc['sk']}",
                f"hashAlg={tc['hashAlg']}",
            ]
    elif tg["signatureInterface"] == "external":
        assert tc["hashAlg"] == "none"
        assert len(tc["context"]) <= 2 * 255
        assert len(tc["message"]) <= 2 * 65536

        acvp_call = exec_prefix + [
            acvp_bin,
            "sigGen",
            f"message={tc['message']}",
            f"rnd={tc['rnd']}",
            f"sk={tc['sk']}",
            f"context={tc['context']}",
        ]
    else:  # signatureInterface=internal
        assert tc["hashAlg"] == "none"
        externalMu = 0
        if tg["externalMu"] is True:
            externalMu = 1
            assert len(tc["mu"]) == 2 * 64
            msg = tc["mu"]
        else:
            assert len(tc["message"]) <= 2 * 65536
            msg = tc["message"]

        acvp_call = exec_prefix + [
            acvp_bin,
            "sigGenInternal",
            f"message={msg}",
            f"rnd={tc['rnd']}",
            f"sk={tc['sk']}",
            f"externalMu={externalMu}",
        ]

    result = subprocess.run(acvp_call, encoding="utf-8", capture_output=True)
    if result.returncode != 0:
        err("FAIL!")
        err(f"{acvp_call} failed with error code {result.returncode}")
        err(result.stderr)
        exit(1)
    # Extract results and compare to expected data
    for l in result.stdout.splitlines():
        (k, v) = l.split("=")
        if v != tc[k]:
            err("FAIL!")
            err(f"Mismatching result for {k}: expected {tc[k]}, got {v}")
            exit(1)
    info("OK")


def run_sigVer_test(tg, tc):
    info(f"Running sigVer test case {tc['tcId']} ... ", end="")
    acvp_bin = get_acvp_binary(tg)

    if tg["preHash"] == "preHash":
        assert len(tc["context"]) <= 2 * 255

        # Use specialized SHAKE256 function that computes hash internally
        if tc["hashAlg"] == "SHAKE-256":
            acvp_call = exec_prefix + [
                acvp_bin,
                "sigVerPreHashShake256",
                f"message={tc['message']}",
                f"context={tc['context']}",
                f"signature={tc['signature']}",
                f"pk={tc['pk']}",
            ]
        else:
            ph = compute_hash(tc["message"], tc["hashAlg"])
            acvp_call = exec_prefix + [
                acvp_bin,
                "sigVerPreHash",
                f"ph={ph}",
                f"context={tc['context']}",
                f"signature={tc['signature']}",
                f"pk={tc['pk']}",
                f"hashAlg={tc['hashAlg']}",
            ]
    elif tg["signatureInterface"] == "external":
        assert tc["hashAlg"] == "none"
        assert len(tc["context"]) <= 2 * 255
        assert len(tc["message"]) <= 2 * 65536

        acvp_call = exec_prefix + [
            acvp_bin,
            "sigVer",
            f"message={tc['message']}",
            f"context={tc['context']}",
            f"signature={tc['signature']}",
            f"pk={tc['pk']}",
        ]
    else:  # signatureInterface=internal
        assert tc["hashAlg"] == "none"
        externalMu = 0
        if tg["externalMu"] is True:
            externalMu = 1
            assert len(tc["mu"]) == 2 * 64
            msg = tc["mu"]
        else:
            assert len(tc["message"]) <= 2 * 65536
            msg = tc["message"]

        acvp_call = exec_prefix + [
            acvp_bin,
            "sigVerInternal",
            f"message={msg}",
            f"signature={tc['signature']}",
            f"pk={tc['pk']}",
            f"externalMu={externalMu}",
        ]

    result = subprocess.run(acvp_call, encoding="utf-8", capture_output=True)

    if (result.returncode == 0) != tc["testPassed"]:
        err("FAIL!")
        err(
            f"Mismatching verification result: expected {tc['testPassed']}, got {result.returncode == 0}"
        )
        exit(1)
    info("OK")


def runTestSingle(internalProjectionName, internalProjection):
    info(f"Running ACVP tests for {internalProjectionName}")

    assert internalProjection["algorithm"] == "ML-DSA"
    assert (
        internalProjection["mode"] == "keyGen"
        or internalProjection["mode"] == "sigGen"
        or internalProjection["mode"] == "sigVer"
    )

    # copy top level fields into the results
    results = internalProjection.copy()

    results["testGroups"] = []
    for tg in internalProjection["testGroups"]:
        tgResult = {
            "tgId": tg["tgId"],
            "tests": [],
        }
        results["testGroups"].append(tgResult)
        for tc in tg["tests"]:
            if internalProjection["mode"] == "keyGen":
                result = run_keyGen_test(tg, tc)
            elif internalProjection["mode"] == "sigGen":
                result = run_sigGen_test(tg, tc)
            elif internalProjection["mode"] == "sigVer":
                result = run_sigVer_test(tg, tc)
            tgResult["tests"].append(result)


def runTest(data):
    for internalProjectionName, internalProjection in data:
        runTestSingle(internalProjectionName, internalProjection)
    info("ALL GOOD!")


def test(version="v1.1.0.40"):
    # load data from downloaded files
    data = loadDefaultAcvpData(version)

    runTest(data)


parser = argparse.ArgumentParser()

parser.add_argument(
    "--version",
    "-v",
    default="v1.1.0.40",
    help="ACVP test vector version (default: v1.1.0.40)",
)
args = parser.parse_args()

# Download files if needed
if not download_acvp_files(args.version):
    print("Failed to download ACVP test files", file=sys.stderr)
    sys.exit(1)

test(args.version)
