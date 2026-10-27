# 本地 Lean4 可复现代码相关产物 / Local Lean 4 reproduction

本目录收录最新英文论文（修订日期 2026-10-27）对应的原始 **Lean 4.33.1 本地形式化证明产物**：1,199 个证明源码、固定外部依赖及 103 项冻结声明的精确类型和公理检查。它与仓库顶层的 Lean 4.35.0-rc2 Palomar 版本分别维护。

本次验证范围：使用固定的预编译外部库，从源码重新编译全部 1,199 个论文模块（包括 `GoalRoot`），然后运行 103 项类型/公理检查。允许的公理仅为 `propext`、`Classical.choice`、`Quot.sound`。这不是 Lean 编译器及全部外部库的从零构建，也不签发新版论文的原项目合同审计或 Palomar 语义验收。

## 环境

- Linux x86-64，兼容官方 Lean 4.33.1 二进制工具链的 glibc。
- Python 3.8 或更新版本；复现与下载脚本仅使用标准库，无需 Conda、模型账户或原服务器 `/home` 目录。
- 完整 Lean **4.33.1** 安装（包括标准库）。可通过 Elan 安装 `leanprover/lean4:v4.33.1`，或使用官方解压后的工具链。
- Mathlib 固定提交 `0df444a360eaa60ab8c11dca51a86af692955474`（v4.33.1）。其所需模块已包含在依赖中，无需另行下载一份 Mathlib。依赖还包括本地 `Definitions`、`Theorems`、`P2M` 及 Batteries、Aesop 等库。
- 建议至少 32 GiB 可用内存和 20 GiB 可用磁盘；个别几何模块可能需要超过 20 GiB 内存。默认两个编译进程、每进程一个 Lean 线程；内存紧张时使用 `--jobs 1`。

## 下载和重建

从仓库根目录进入此目录，确保使用本目录的 `lean-toolchain`：

```bash
cd local-reproduction
# 如使用 Elan，先安装指定工具链：
elan toolchain install leanprover/lean4:v4.33.1

# 首次下载同仓库 Release 中的外部预编译依赖，并逐文件校验：
python3 scripts/fetch_dependencies.py

# 使用尚不存在的构建目录，全量重编译后复核 103 项声明：
python3 scripts/reproduce.py --jobs 2 --lean-threads 1 --build-dir build-fresh
```

如果不使用 Elan，指定已有工具链的编译器即可：

```bash
python3 scripts/reproduce.py --lean /path/to/lean-4.33.1/bin/lean \
  --jobs 2 --lean-threads 1 --build-dir build-fresh
```

脚本验证版本，自动查询工具链前缀，清除继承的 Lean/Lake 和动态库覆盖路径；导入路径只包括本次构建目录、这里的 `dependencies/lib/lean` 与所选工具链标准库。脚本不依赖仓库顶层 Lake 环境。输入 `SHA256SUMS` 在编译前后均验证；`--verify-checksums` 兼容参数可省略，因为校验始终启用。

结果写入 `build-fresh/VerificationReport.json`，模块和声明日志位于 `build-fresh/logs/`。成功结果必须显示 `passed: true`、`fresh_modules: 1199`、`exact_type_checks: 103`。只查看随论文附带的旧报告不能代替本机执行。

重查已有的成功构建可使用 `--verify-only --build-dir build-fresh`；这会检查对象齐备并重新执行 103 个探针，不重新编译 1,199 个模块，结果单独写入 `ReverificationReport.json`。

## 依赖附件和离线使用

外部编译文件约 7.56 GiB，单个文件最大超过 GitHub 普通 Git 的 100 MiB 限制。因此源码保存在 Git，二进制文件发布在本仓库 Release **`local-lean4331-reproduction-20261027`**，下载地址、大小与 SHA-256 在 `metadata/dependency-assets.json`。下载器把它们恢复到所要求的 `dependencies/lib/lean/`。

可在联网机器下载该 Release 的全部 `theta-lean4331-dependencies-*.zip`，拷贝到离线机器后执行：

```bash
python3 scripts/fetch_dependencies.py --asset-dir /path/to/downloaded-assets
python3 scripts/reproduce.py --lean /path/to/lean-4.33.1/bin/lean --jobs 2 --build-dir build-fresh
```

离线机器还需事先安装 Lean 工具链与 Python。GitHub 的 “Download ZIP” 源码包不含 Release 附件。完成依赖安装后可移除 `.downloads/` 下载缓存；`dependencies/lib/lean/` 是复现输入，不能在构建期间删除。

## 目录

- `Lean/`：最新交付中的 1,199 个原样证明源码。
- `dependencies/src/`：11,403 个外部模块源码及 15 个嵌入资源；`dependencies/lib/lean/`：下载后恢复的 46,163 个编译相关文件。
- `scripts/`：依赖下载/校验与本地独立复现入口。
- `metadata/dependencies.json`：导入关系与原始依赖解析来源。
- `metadata/original-contract.json`：原始冻结的 103 项义务；与最新 editorial 合同的义务逐项一致。
- `metadata/packages/`：原依赖包配置、版本和可获取的许可证。第三方代码沿用各自许可证与作者信息；本包不重新许可这些库。
- `verification/probes/`：103 个精确类型与公理探针。
- `publication/`：最新论文、形式化映射、原项目复现说明和历史审计报告。
- `SHA256SUMS`：固定输入校验清单，包括经 Release 提供的外部编译文件。

`publication/Reproduce.md` 原样保留原项目合同审计说明，其中的服务器路径不是本目录的复现入口。独立复现使用本文件。元数据中的原服务器路径只是来源记录，本目录脚本不会按这些绝对路径寻找依赖。旧合同与探针的配对由校验清单固定；它们不表示本次重新进行了新版论文合同审计。

## English scope

These are the original **local Lean 4.33.1 reproducibility artifacts** for the paper revised on 27 October 2026, separate from the repository's Palomar port. Install Lean 4.33.1 and Python, run `scripts/fetch_dependencies.py`, then `scripts/reproduce.py` from this directory. All 1,199 delivered proof modules are recompiled against pinned, precompiled external libraries, followed by 103 frozen exact-type/axiom checks. Sources and dependency assets are hash-checked before and after verification. This does not claim a cold rebuild of external libraries, a new original-project editorial audit, or Palomar semantic acceptance.
