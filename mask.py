#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
mask.py — 客服工单 CSV 脱敏工具

处理五类敏感信息：手机号、身份证号、邮箱、银行卡号、员工姓名。
- 同一真实值（不区分写法：空格/横线/+86、大小写邮箱、带分隔符卡号）映射到同一个假值。
- 假值保留原写法格式（分隔符、+86 前缀、卡号分组、15/18 位身份证长度）。
- 姓名只替换 names.txt 名单中的名字，且优先匹配最长名字（王伟明 不会被拆成 王伟 + 明）。
- 不含敏感信息的文本原样保留。

输出：
  tickets_masked.csv                     可交付版本
  INTERNAL_mapping_do_not_distribute.csv 真假对照（内部留存，禁止外发）
  mask_report.txt                        脱敏报告（含抽检核验结果）

用法：
  python3 mask.py --input tickets.csv --names names.txt \
      --sample accept_sample.txt --out-dir .
"""

from __future__ import annotations

import argparse
import csv
import random
import re
import sys
from collections import Counter, OrderedDict, defaultdict
from datetime import datetime
from pathlib import Path

TYPES = ("手机号", "身份证", "邮箱", "银行卡", "姓名")

# 占位符使用私用区字符 + 纯字母序号，保证不会与任何待识别模式（需要数字/中文/邮箱）冲突
PH_LEFT = ""
PH_RIGHT = ""
PH_RE = re.compile(PH_LEFT + "([A-Z]+)" + PH_RIGHT)

PHONE_LIKE_RE = re.compile(r"1[3-9]\d{9}")


def has_phone_fragment(digits: str) -> bool:
    """检查是否为手机号，或任意 11 位窗口看起来像手机号。"""
    if PHONE_LIKE_RE.fullmatch(digits):
        return True
    return any(PHONE_LIKE_RE.fullmatch(digits[i:i + 11])
               for i in range(len(digits) - 10))



def token_of(n: int) -> str:
    """0 -> A, 25 -> Z, 26 -> AA ..."""
    n += 1
    out = []
    while n:
        n, r = divmod(n - 1, 26)
        out.append(chr(65 + r))
    return "".join(reversed(out))


# ---------------------------------------------------------------- 号码工具

ID_WEIGHTS = (7, 9, 10, 5, 8, 4, 2, 1, 6, 3, 7, 9, 10, 5, 8, 4, 2)
ID_CHECK = "10X98765432"


def id18_checksum(body17: str) -> str:
    s = sum(int(body17[i]) * ID_WEIGHTS[i] for i in range(17))
    return ID_CHECK[s % 11]


def valid_id18(s: str) -> bool:
    return len(s) == 18 and id18_checksum(s[:17]) == s[17].upper()


def valid_yymmdd(s: str) -> bool:
    if len(s) != 6 or not s.isdigit():
        return False
    yy, mm, dd = int(s[:2]), int(s[2:4]), int(s[4:6])
    year = 2000 + yy if yy <= 30 else 1900 + yy
    if not (1 <= mm <= 12):
        return False
    leap = year % 4 == 0 and (year % 100 != 0 or year % 400 == 0)
    days = [31, 29 if leap else 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
    return 1 <= dd <= days[mm - 1]


def digits_only(s: str) -> str:
    return "".join(ch for ch in s if ch.isdigit())


def luhn_check_digit(body: str) -> str:
    """给定不含校验位的卡号主体，返回 Luhn 校验位。"""
    total = 0
    for i, ch in enumerate(reversed(body)):
        d = int(ch)
        if i % 2 == 0:          # 校验位位于最右，主体倒数第 1 位开始需加倍
            d *= 2
            if d > 9:
                d -= 9
        total += d
    return str((10 - total % 10) % 10)


def digit_groups(text: str):
    """提取文本中由单个空格/横线连接的连续数字串（去掉分隔符后的形态）。"""
    for m in re.finditer(r"\d(?:[ \-]?\d)*", text):
        yield m.group(0).replace(" ", "").replace("-", "")


# ---------------------------------------------------------------- 脱敏器

class Masker:
    def __init__(self, names, seed: int, name_blacklist_text: str = ""):
        self.rng = random.Random(seed)
        self.names = list(names)
        self.name_set = set(names)
        self.corpus_text = name_blacklist_text

        self.maps = {t: OrderedDict() for t in TYPES}     # 真实值 -> 假值（首次出现顺序）
        self.variants = {t: defaultdict(Counter) for t in TYPES}  # 真实值 -> 原始写法计数
        self.fake_used = {t: set() for t in TYPES}
        self.records = []                                 # (token, type, real, fake, original)
        self.token_index = {}
        self.ticket_stats = defaultdict(
            lambda: defaultdict(lambda: {"real": set(), "fake": set(), "count": 0})
        )
        self.ticket = None
        self.bad_checksums = []
        self.exempt_numbers = set()   # 校验位不通过且无上下文，明确不按身份证处理

        # 假值素材
        self.email_seq = 0
        self.card_bins = ["622202", "622588", "622260", "622848", "622700",
                          "436742", "456735"]
        self.id_areas = ["110101", "310104", "440106", "510107", "330102",
                         "120101", "320102", "370102", "420102", "610102"]
        self.name_surnames = list("沈韩蒋蔡潘田姜范方石姚谭廖邹熊陆郝孔白崔康毛邱秦江史顾尹")
        self.name_givens = ["嘉怡", "思远", "子墨", "雨桐", "明轩", "诗涵", "俊杰", "欣然",
                            "若彤", "宇航", "佳宁", "皓宇", "芷晴", "天佑", "梦洁", "浩然",
                            "婉清", "泽楷", "亦菲", "书瑶", "晨曦", "一鸣", "安琪", "博文"]

    # ---- 记录与占位

    def _record(self, typ, real, fake, original):
        tok = token_of(len(self.records))
        self.records.append((tok, typ, real, fake, original))
        self.token_index[tok] = self.records[-1]
        st = self.ticket_stats[self.ticket][typ]
        st["real"].add(real)
        st["fake"].add(fake)
        st["count"] += 1
        self.variants[typ][real][original] += 1
        return PH_LEFT + tok + PH_RIGHT

    def _fake_for(self, typ, real, factory):
        fake = self.maps[typ].get(real)
        if fake is None:
            fake = factory()
            self.maps[typ][real] = fake
        return fake

    # ---- 各类识别

    EMAIL_RE = re.compile(r"[A-Za-z0-9._%+\-]+@[A-Za-z0-9.\-]+\.[A-Za-z]{2,}")

    def mask_emails(self, text):
        def repl(m):
            raw = m.group(0)
            key = raw.lower()
            fake = self._fake_for("邮箱", key, self._new_email)
            return self._record("邮箱", key, fake, raw)
        return self.EMAIL_RE.sub(repl, text)

    def _new_email(self):
        while True:
            self.email_seq += 1
            cand = f"masked.user{self.email_seq:03d}@example.com"
            if cand not in self.fake_used["邮箱"]:
                self.fake_used["邮箱"].add(cand)
                return cand

    ID18_RE = re.compile(r"(?<![\dA-Za-z])\d{17}[\dXx](?![\dA-Za-z])")
    ID15_RE = None  # 见 mask_ids：15 位身份证的边界需按上下文判断

    CW_RE = re.compile(r"卡号|银行卡")
    ID_CTX_RE = re.compile(r"证件|身份证")

    def mask_ids(self, text):
        def repl18(m):
            raw = m.group(0)
            key = raw.upper()
            # 紧邻“卡号/银行卡”且无证件类提示时，留给银行卡规则处理
            if self._ctx(self.CW_RE, text, m.start(), m.end()) and \
                    not self._ctx(self.ID_CTX_RE, text, m.start(), m.end()):
                return raw
            if not valid_id18(key):
                if not self._ctx(self.ID_CTX_RE, text, m.start(), m.end()):
                    self.bad_checksums.append(key)
                    self.exempt_numbers.add(key)
                    return raw
            fake = self._fake_for("身份证", key, self._new_id18)
            return self._record("身份证", key, fake, raw)

        text = self.ID18_RE.sub(repl18, text)

        def repl15(m):
            raw = m.group(0)
            # 15 位无校验位，必须日期合法，或紧邻“身份证/证件”等字样才认定
            if not valid_yymmdd(raw[6:12]):
                if not self._ctx(self.ID_CTX_RE, text, m.start(), m.end()):
                    return raw
            key = raw
            fake = self._fake_for("身份证", key, self._new_id15)
            return self._record("身份证", key, fake, raw)

        return re.sub(r"(?<![\dA-Za-z])\d{15}(?![\dA-Za-z])", repl15, text)

    @staticmethod
    def _ctx(pattern, text, start, end, width=10):
        return bool(pattern.search(text[max(0, start - width):min(len(text), end + width)]))

    def mask_cards(self, text):
        # 16~19 位，允许数字之间有一个空格或横线
        pat = re.compile(r"(?<![\dA-Za-z])(?:\d[ \-]?){15,18}\d(?![\dA-Za-z])")

        def repl(m):
            raw = m.group(0)
            key = digits_only(raw)
            if not (16 <= len(key) <= 19) or key in self.exempt_numbers:
                return raw
            fake = self._fake_for("银行卡", key, lambda: self._new_card(key))
            return self._record("银行卡", key, fake, raw)

        return pat.sub(repl, text)

    def mask_phones(self, text):
        # 可带 +86，国内号段 1[3-9]，数字间允许空格或横线
        pat = re.compile(r"(?<![\dA-Za-z])(?:\+86[ \-]?)?1[3-9]\d(?:[ \-]?\d){8}(?![\dA-Za-z])")

        def repl(m):
            raw = m.group(0)
            key = digits_only(raw)
            if len(key) == 13 and key.startswith("86"):
                key = key[2:]
            if len(key) != 11:
                return raw
            fake = self._fake_for("手机号", key, self._new_phone)
            return self._record("手机号", key, fake, raw)

        return pat.sub(repl, text)

    def mask_names(self, text):
        if not self.names:
            return text
        ordered = sorted(self.names, key=len, reverse=True)
        pat = re.compile(
            r"(?<![A-Za-z0-9])(?:" + "|".join(re.escape(n) for n in ordered) + r")(?![A-Za-z0-9])"
        )

        def repl(m):
            key = m.group(0)
            fake = self._fake_for("姓名", key, lambda: self._new_name())
            return self._record("姓名", key, fake, key)

        return pat.sub(repl, text)

    # ---- 假值生成

    def _new_phone(self):
        while True:
            cand = "199" + "".join(str(self.rng.randint(0, 9)) for _ in range(8))
            if cand not in self.fake_used["手机号"]:
                self.fake_used["手机号"].add(cand)
                return cand

    def _rand_date(self, day_len_digits):
        """生成 YYMMDD（6 位）或 YYYYMMDD（8 位）生日。"""
        if day_len_digits == 6:
            return f"{self.rng.randint(65, 99):02d}{self.rng.randint(1, 12):02d}{self.rng.randint(1, 28):02d}"
        return f"{self.rng.randint(1965, 2002)}{self.rng.randint(1, 12):02d}{self.rng.randint(1, 28):02d}"

    def _new_id18(self):
        for _attempt in range(1000):
            body = self.rng.choice(self.id_areas) + self._rand_date(8) + \
                   f"{self.rng.randint(1, 999):03d}"
            if len(body) != 17:
                raise AssertionError(f"bad id body length {len(body)}")
            cand = body + id18_checksum(body)
            if cand not in self.fake_used["身份证"] and not has_phone_fragment(cand):
                self.fake_used["身份证"].add(cand)
                return cand
        raise RuntimeError("无法生成 18 位假身份证号")

    def _new_id15(self):
        for _attempt in range(1000):
            cand = self.rng.choice(self.id_areas) + self._rand_date(6) + \
                   f"{self.rng.randint(1, 999):03d}"
            if len(cand) != 15:
                raise AssertionError(f"bad id15 length {len(cand)}")
            if cand not in self.fake_used["身份证"] and not has_phone_fragment(cand):
                self.fake_used["身份证"].add(cand)
                return cand
        raise RuntimeError("无法生成 15 位假身份证号")

    def _new_card(self, real):
        """生成同长度的假卡号：前 6 位用合法卡 BIN 段，末位补齐 Luhn 校验。

        BIN 段刻意不含数字 1，避免固定前缀本身就把号码后半段顶成 170xxxxxxx 之类
        的手机号片段，导致下面这组约束永远无法满足。
        """
        n = len(real)
        for _attempt in range(1000):
            bin6 = self.rng.choice(self.card_bins)
            body = bin6 + "".join(str(self.rng.randint(0, 9)) for _ in range(n - 7))
            cand = body + luhn_check_digit(body)
            if cand not in self.fake_used["银行卡"] and cand != real \
                    and not has_phone_fragment(cand):
                self.fake_used["银行卡"].add(cand)
                return cand
        # 兜底：放宽“不含手机号片段”的约束，优先保证一定能产出结果
        for _attempt in range(1000):
            bin6 = self.rng.choice(self.card_bins)
            body = bin6 + "".join(str(self.rng.randint(0, 9)) for _ in range(n - 7))
            cand = body + luhn_check_digit(body)
            if cand not in self.fake_used["银行卡"] and cand != real:
                self.fake_used["银行卡"].add(cand)
                return cand
        raise RuntimeError(f"无法为长度 {n} 的卡号生成假值")

    def _new_name(self):
        for _attempt in range(1000):
            cand = self.rng.choice(self.name_surnames) + self.rng.choice(self.name_givens)
            if cand in self.name_set or cand in self.fake_used["姓名"]:
                continue
            if any(cand in r or r in cand for r in self.name_set):
                continue
            if cand in self.corpus_text:
                continue
            self.fake_used["姓名"].add(cand)
            return cand
        raise RuntimeError("无法生成不与真实姓名冲突的假姓名")

    # ---- 假值回填（保留原始写法格式）

    def render(self, text):
        def repl(m):
            _, typ, real, fake, original = self.token_index[m.group(1)]
            if typ in ("邮箱", "姓名"):
                return fake
            return self._render_numeric(original, fake)
        return PH_RE.sub(repl, text)

    @staticmethod
    def _render_numeric(original, fake):
        digits = digits_only(original)
        if len(digits) == len(fake):
            prefix = 0
        elif len(fake) == 11 and len(digits) == 13 and digits.startswith("86"):
            prefix = 2          # 保留 +86 国家码
        else:
            return fake
        it = iter(fake)
        out = []
        seen = 0
        for ch in original:
            if ch.isdigit():
                seen += 1
                out.append(ch if seen <= prefix else next(it))
            else:
                out.append(ch)
        return "".join(out)


# ---------------------------------------------------------------- 读写

def read_rows(path: Path):
    with open(path, encoding="utf-8-sig", newline="") as f:
        reader = csv.reader(f)
        header = next(reader)
        rows = [(r[0], r[1]) for r in reader if r and len(r) >= 2]
    return header, rows


def read_names(path: Path):
    with open(path, encoding="utf-8-sig") as f:
        return [line.strip() for line in f if line.strip()]


def read_sample(path: Path):
    out = []
    with open(path, encoding="utf-8-sig") as f:
        for lineno, line in enumerate(f):
            line = line.strip()
            if not line:
                continue
            parts = line.split()
            if len(parts) < 2:
                continue
            if lineno == 0 and not re.match(r"^GD-\d+$", parts[0]):
                continue
            out.append((parts[0], parts[1]))
    return out


# ---------------------------------------------------------------- 核验

def find_numbers(text):
    """提取数字串（忽略单个空格/横线分隔），并把带 X 校验位的 18 位号码整体保留。"""
    out = set(digit_groups(text))
    out |= {m.group(0).upper() for m in
            re.finditer(r"(?<![\dA-Za-z])\d{17}[Xx](?![\dA-Za-z])", text)}
    return out


def contains_fake(text, typ, fake):
    if typ == "邮箱":
        return fake.lower() in text.lower()
    if typ == "姓名":
        return fake in text
    groups = find_numbers(text)
    return any(g == fake or (len(g) == 13 and g.startswith("86") and g[2:] == fake)
               for g in groups)


def residual_present(text, typ, real):
    if typ == "邮箱":
        return real.lower() in [e.lower() for e in Masker.EMAIL_RE.findall(text)]
    if typ == "姓名":
        return real in text
    groups = find_numbers(text)
    return any(real.upper() in g.upper() for g in groups)


# ---------------------------------------------------------------- 主流程

def main(argv=None):
    ap = argparse.ArgumentParser(description="客服工单 CSV 脱敏")
    ap.add_argument("--input", default="tickets.csv")
    ap.add_argument("--names", default="names.txt")
    ap.add_argument("--sample", default="accept_sample.txt")
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--masked-name", default="tickets_masked.csv")
    ap.add_argument("--mapping-name", default="INTERNAL_mapping_do_not_distribute.csv")
    ap.add_argument("--internal-dir", default="internal",
                    help="真假对照的存放子目录，与交付文件物理隔离")
    ap.add_argument("--report-name", default="mask_report.txt")
    ap.add_argument("--seed", type=int, default=20261114)
    args = ap.parse_args(argv)

    in_path = Path(args.input)
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    header, rows = read_rows(in_path)
    names = read_names(Path(args.names))
    corpus_text = "\n".join(r[1] for r in rows)

    m = Masker(names, args.seed, corpus_text)
    masked_rows = []
    for code, body in rows:
        m.ticket = code
        t = body
        t = m.mask_emails(t)
        t = m.mask_ids(t)
        t = m.mask_cards(t)
        t = m.mask_phones(t)
        t = m.mask_names(t)
        masked_rows.append((code, m.render(t)))
    masked_by_code = dict(masked_rows)

    # 输出可交付 CSV
    masked_path = out_dir / args.masked_name
    with open(masked_path, "w", encoding="utf-8-sig", newline="") as f:
        w = csv.writer(f, lineterminator="\n", quoting=csv.QUOTE_MINIMAL)
        w.writerow(header)
        w.writerows(masked_rows)

    # 输出真假对照（内部）：放在单独的 internal/ 子目录，避免误随交付文件一并外发
    internal_dir = out_dir / args.internal_dir
    internal_dir.mkdir(parents=True, exist_ok=True)
    mapping_path = internal_dir / args.mapping_name
    with open(mapping_path, "w", encoding="utf-8-sig", newline="") as f:
        w = csv.writer(f, lineterminator="\n")
        w.writerow(["类型", "真实值", "假值", "出现次数", "出现写法", "涉及工单"])
        for typ in TYPES:
            for real, fake in m.maps[typ].items():
                occurs = sum(m.variants[typ][real].values())
                variants = " | ".join(sorted(m.variants[typ][real]))
                tickets = sorted({c for c, _ in rows
                                  if c in m.ticket_stats and typ in m.ticket_stats[c]
                                  and real in m.ticket_stats[c][typ]["real"]})
                w.writerow([typ, real, fake, occurs, variants, ",".join(tickets)])
    try:
        mapping_path.chmod(0o600)   # 仅本人可读，进一步降低误外发风险
    except OSError:
        pass

    # ---- 统计
    counts = Counter()
    tickets_per_type = defaultdict(set)
    for typ in TYPES:
        for real in m.maps[typ]:
            n = sum(m.variants[typ][real].values())
            counts[typ] += n
            tickets_per_type[typ].update(
                c for c, _ in rows if typ in m.ticket_stats.get(c, {})
                and real in m.ticket_stats[c][typ]["real"]
            )
    total = sum(counts.values())
    untouched = [c for c, body in rows if c not in m.ticket_stats]

    # ---- 抽检逐条核验
    sample = read_sample(Path(args.sample)) if Path(args.sample).exists() else []
    sample_results = []
    for code, typ in sample:
        if typ not in TYPES:
            sample_results.append((code, typ, "FAIL", "未知类型"))
            continue
        if code not in masked_by_code:
            sample_results.append((code, typ, "FAIL", "工单不存在"))
            continue
        st = m.ticket_stats.get(code, {}).get(typ)
        masked_text = masked_by_code[code]
        if not st or st["count"] == 0:
            sample_results.append((code, typ, "FAIL", "未检测到该类型敏感信息"))
            continue
        left = [r for r in st["real"] if residual_present(masked_text, typ, r)]
        if left:
            sample_results.append((code, typ, "FAIL", f"残留原值 {len(left)} 个"))
            continue
        if not any(contains_fake(masked_text, typ, f) for f in st["fake"]):
            sample_results.append((code, typ, "FAIL", "未找到对应假值"))
            continue
        sample_results.append(
            (code, typ, "PASS", f"替换 {st['count']} 处，原值已清除，假值一致")
        )
    sample_pass = sum(1 for r in sample_results if r[2] == "PASS")

    # ---- 全局残留扫描
    all_masked = "\n".join(b for _, b in masked_rows)
    global_left = []
    for typ in TYPES:
        for real in m.maps[typ]:
            if residual_present(all_masked, typ, real):
                global_left.append((typ, real))

    # 假值不应与任何真实值撞车
    collisions = []
    for typ in TYPES:
        reals = set(m.maps[typ])
        for fake in m.maps[typ].values():
            if residual_present(all_masked, typ, fake) and fake in reals:
                collisions.append((typ, fake))

    # ---- 报告
    lines = []
    add = lines.append
    add("客服工单脱敏报告")
    add("=" * 60)
    add(f"生成时间：{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    add(f"输入：{in_path}（{len(rows)} 条工单）")
    add(f"可交付文件：{masked_path}")
    add(f"内部对照文件（禁止外发）：{mapping_path}")
    add("")
    add("一、替换统计")
    add("-" * 60)
    add(f"{'类型':<6}{'真实值个数':>10}{'替换处数':>10}{'涉及工单数':>12}")
    for typ in TYPES:
        add(f"{typ:<6}{len(m.maps[typ]):>10}{counts[typ]:>10}{len(tickets_per_type[typ]):>12}")
    add(f"{'合计':<6}{sum(len(m.maps[t]) for t in TYPES):>10}{total:>10}"
        f"{len({c for c, _ in rows if c in m.ticket_stats}):>12}")
    add("")
    add("二、多写法归并情况（不展示真实值）")
    add("-" * 60)
    for typ in ("手机号", "身份证", "银行卡", "邮箱"):
        multi = sum(1 for vc in m.variants[typ].values() if len(vc) > 1)
        max_forms = max((len(vc) for vc in m.variants[typ].values()), default=0)
        if m.variants[typ]:
            add(f"{typ}：{multi} 个真实值存在多种写法，已全部归并为同一假值"
                f"（单个真实值最多出现 {max_forms} 种写法）")
    add("")
    add("三、抽检条款逐条核验")
    add("-" * 60)
    if sample_results:
        for code, typ, res, note in sample_results:
            add(f"{code}  {typ:<4}  {res}  {note}")
        add(f"结果：{sample_pass}/{len(sample_results)} 通过")
    else:
        add("未提供抽检清单")
    add("")
    add("四、全局残留扫描")
    add("-" * 60)
    if global_left:
        add(f"发现残留 {len(global_left)} 处：")
        for typ, real in global_left:
            add(f"  {typ} {real}")
    else:
        add("未发现任何真实手机号 / 身份证号 / 邮箱 / 银行卡号 / 名单姓名残留。")
    if collisions:
        add(f"发现真假值冲突 {len(collisions)} 处，请重新生成。")
    if m.bad_checksums:
        add(f"注意：{len(m.bad_checksums)} 个 18 位号码校验位不通过且无上下文，未按身份证处理。")
    if untouched:
        add(f"未含敏感信息、原文未改动的工单（{len(untouched)} 条）："
            + "、".join(untouched))
    add("")
    add("五、外发注意事项")
    add("-" * 60)
    add(f"1. 只能外发 {masked_path.name}；")
    add(f"2. {mapping_path.name} 含真实值，仅限内部留存，严禁随数据发出；")
    add("3. 同一真实值在全部工单中已映射为同一假值，外包方可据此对齐。")
    report = "\n".join(lines) + "\n"

    report_path = out_dir / args.report_name
    report_path.write_text(report, encoding="utf-8")
    print(report)

    # 退出码：抽检或残留有问题时置为非 0
    ok = (not global_left) and (not collisions) and \
         (sample_pass == len(sample_results))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
