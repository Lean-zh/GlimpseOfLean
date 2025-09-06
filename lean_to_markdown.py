#!/usr/bin/env python3
"""
Lean to Markdown Converter

This script converts Lean files to Markdown format by:
1. Converting block comments (/* ... */) to markdown text
2. Converting code sections to ```lean code blocks
3. Preserving inline comments (--) as part of the code

Usage: python lean_to_markdown.py <input_folder> <output_folder> [--prefix PREFIX]
"""

import os
import sys
import re
import argparse
from pathlib import Path

def parse_lean_file(content):
    """
    Parse Lean file content and convert to markdown format.
    
    Args:
        content (str): The content of the Lean file
        
    Returns:
        str: Converted markdown content
    """
    result = []
    lines = content.split('\n')
    i = 0
    in_block_comment = False
    in_code_block = False
    code_buffer = []
    
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()
        
        # Check for start of block comment
        if '/-' in line and not in_block_comment:
            # If we have accumulated code, output it first
            if code_buffer:
                result.append('```lean')
                result.extend(code_buffer)
                result.append('```\n')
                code_buffer = []
                in_code_block = False
            
            # Handle block comment
            comment_start = line.find('/-')
            before_comment = line[:comment_start].strip()
            
            # Add any code before the comment
            if before_comment:
                code_buffer.append(line[:comment_start].rstrip())
                if code_buffer:
                    result.append('```lean')
                    result.extend(code_buffer)
                    result.append('```\n')
                    code_buffer = []
            
            # Start collecting comment content
            comment_content = line[comment_start + 2:]
            in_block_comment = True
            
            # Check if comment ends on same line
            if '-/' in comment_content:
                end_pos = comment_content.find('-/')
                comment_text = comment_content[:end_pos].strip()
                if comment_text:
                    result.append(comment_text)
                    result.append('')  # Add blank line
                
                # Handle any code after the comment on same line
                after_comment = comment_content[end_pos + 2:].strip()
                if after_comment:
                    code_buffer.append(after_comment)
                    in_code_block = True
                
                in_block_comment = False
            else:
                # Multi-line comment
                if comment_content.strip():
                    result.append(comment_content.strip())
        
        # Check for end of block comment
        elif '-/' in line and in_block_comment:
            end_pos = line.find('-/')
            comment_part = line[:end_pos].strip()
            if comment_part:
                result.append(comment_part)
            
            result.append('')  # Add blank line after comment
            
            # Handle any code after the comment
            after_comment = line[end_pos + 2:].strip()
            if after_comment:
                code_buffer.append(after_comment)
                in_code_block = True
            
            in_block_comment = False
        
        # Handle content inside block comment
        elif in_block_comment:
            result.append(line)
        
        # Handle regular code lines
        else:
            # Skip empty lines at the beginning
            if stripped or code_buffer or in_code_block:
                code_buffer.append(line)
                in_code_block = True
        
        i += 1
    
    # Output any remaining code
    if code_buffer:
        result.append('```lean')
        result.extend(code_buffer)
        result.append('```')
    
    return '\n'.join(result)

def convert_file(input_path, output_path):
    """
    Convert a single Lean file to Markdown.
    
    Args:
        input_path (Path): Path to input Lean file
        output_path (Path): Path to output Markdown file
    """
    try:
        with open(input_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        markdown_content = parse_lean_file(content)
        
        # Ensure output directory exists
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(markdown_content)
        
        print(f"Converted: {input_path} -> {output_path}")
        
    except Exception as e:
        print(f"Error converting {input_path}: {e}")

def convert_directory(input_dir, output_dir, prefix=""):
    """
    Convert all Lean files in a directory to Markdown, preserving structure.
    
    Args:
        input_dir (Path): Input directory path
        output_dir (Path): Output directory path
        prefix (str): Prefix to add before .md extension (e.g., "zh" for .zh.md)
    """
    input_path = Path(input_dir)
    output_path = Path(output_dir)
    
    if not input_path.exists():
        print(f"Error: Input directory {input_path} does not exist")
        return
    
    # Find all .lean files
    lean_files = list(input_path.rglob('*.lean'))
    
    if not lean_files:
        print(f"No .lean files found in {input_path}")
        return
    
    print(f"Found {len(lean_files)} Lean files")
    
    for lean_file in lean_files:
        # Calculate relative path to preserve directory structure
        relative_path = lean_file.relative_to(input_path)
        
        # Change extension to .md with optional prefix
        if prefix:
            md_relative_path = relative_path.with_suffix(f'.{prefix}.md')
        else:
            md_relative_path = relative_path.with_suffix('.md')
        
        # Create output path
        output_file = output_path / md_relative_path
        
        convert_file(lean_file, output_file)

def main():
    """
    Main function to handle command line arguments and start conversion.
    """
    parser = argparse.ArgumentParser(
        description='Convert Lean files to Markdown format',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""Examples:
  python lean_to_markdown.py GlimpseOfLean docs
  python lean_to_markdown.py GlimpseOfLean docs --prefix zh
  python lean_to_markdown.py GlimpseOfLean docs --prefix en"""
    )
    
    parser.add_argument('input_folder', help='Input folder containing Lean files')
    parser.add_argument('output_folder', help='Output folder for Markdown files')
    parser.add_argument('--prefix', '-p', default='', 
                       help='Prefix to add before .md extension (e.g., "zh" for .zh.md, "en" for .en.md)')
    
    args = parser.parse_args()
    
    if args.prefix:
        print(f"Converting Lean files from {args.input_folder} to {args.output_folder} with prefix '{args.prefix}'")
    else:
        print(f"Converting Lean files from {args.input_folder} to {args.output_folder}")
    
    convert_directory(args.input_folder, args.output_folder, args.prefix)
    print("Conversion completed!")

if __name__ == "__main__":
    main()