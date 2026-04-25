#!/usr/bin/env python3
# 

import os
import sys
import subprocess
from pathlib import Path

def file_transform(input_file: Path, output_file: Path, command: str):
    """
    Applies a given command-line command to the input file and writes the output to the output file.

    :param input_file: Path to the input file.
    :param output_file: Path to the output file.
    :param command: Command-line command to apply to the input file.
    """
    # Construct the command
    full_command = f"{command} {input_file}"
    
    try:
        # Open the output file and run the command
        with output_file.open("w") as f_out:
            subprocess.run(full_command, shell=True, stdout=f_out, stderr=subprocess.PIPE, check=True)
    except subprocess.CalledProcessError as e:
        print(f"Error processing file {input_file}: {e.stderr.decode()}", file=sys.stderr)

def transform_directory(input_dir: Path, output_dir: Path, transform_function, command: str):
    """
    Transforms a directory of files recursively.

    :param input_dir: Path to the input directory.
    :param output_dir: Path to the output directory.
    :param transform_function: Function to transform files.
    :param command: Command-line command to apply to each file.
    """
    if not input_dir.is_dir():
        raise ValueError(f"{input_dir} is not a valid directory.")

    for root, _, files in os.walk(input_dir):
        # Calculate the relative path
        relative_path = Path(root).relative_to(input_dir)
        # Create the corresponding output directory
        output_subdir = output_dir / relative_path
        output_subdir.mkdir(parents=True, exist_ok=True)

        for file_name in files:
            input_file = Path(root) / file_name

            # Process only .lean files
            if input_file.suffix == ".lean":
                output_file = output_subdir / file_name

                # Apply the transformation
                transform_function(input_file, output_file, command)

if __name__ == "__main__":
    import argparse

    # Set up command-line argument parsing
    parser = argparse.ArgumentParser(description="Transform a directory of files recursively using a given command.")
    parser.add_argument(
        "input_directory",
        nargs="?",
        default=".",
        type=Path,
        help="Path to the input directory (default: current directory)",
    )
    parser.add_argument(
        "output_directory",
        nargs="?",
        default="./output",
        type=Path,
        help="Path to the output directory (default: './output')",
    )
    parser.add_argument(
        "command",
        type=str,
        help="Command-line command to apply to each input file."
    )

    args = parser.parse_args()

    # Get input, output directories, and the command from the command line
    input_directory = args.input_directory.resolve()
    output_directory = args.output_directory.resolve()
    command = args.command

    print(f"Input directory: {input_directory}")
    print(f"Output directory: {output_directory}")
    print(f"Command: {command}")

    try:
        transform_directory(input_directory, output_directory, file_transform, command)
        print("Transformation completed successfully.")
    except Exception as e:
        print(f"Error: {e}")
