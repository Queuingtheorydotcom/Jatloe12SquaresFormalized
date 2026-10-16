"""Read preserved source bytes, including losslessly compressed local provenance.

Compression is a storage choice only. Hashes always describe the original
uncompressed bytes, and these files are never imported by the compact proof.
"""
from pathlib import Path
import gzip
import hashlib


def compressed_path(path):
    """Portable suffix fallback, including already-long recovered filenames."""
    path = Path(path)
    if len((path.name + '.gz').encode('utf-8')) <= 255:
        return path.with_name(path.name + '.gz')
    return path.parent / '.provenance-gzip' / (
        hashlib.sha256(path.name.encode('utf-8')).hexdigest() + '.gz')


def exists(path):
    path = Path(path)
    return path.is_file() or compressed_path(path).is_file()


def binary_stream(path):
    path = Path(path)
    return path.open('rb') if path.is_file() else gzip.open(compressed_path(path), 'rb')


def read_bytes(path):
    with binary_stream(path) as stream:
        return stream.read()


def read_text(path):
    return read_bytes(path).decode('utf-8')


def text_stream(path):
    path = Path(path)
    return path.open() if path.is_file() else gzip.open(
        compressed_path(path), 'rt', encoding='utf-8')
