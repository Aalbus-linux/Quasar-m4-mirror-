/*
 * Copyright (c) 1999 Marc Espie
 * Copyright (c) 2013, 2015 William Haddon
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

#include <sys/param.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <ctype.h>
#include <paths.h>
#include <regex.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <err.h>
#include <errno.h>
#include <unistd.h>
#include "mdef.h"
#include "stdd.h"
#include "extern.h"


int prefix_builtins = 0; /* Add an m4_ prefix to the beginning of all builtin
			functions */
int freeze = 0;
char *freeze_filename;

int restore = 0;
char *restore_filename;

/*
 * Support for include path search
 * First search in the current directory.
 * If not found, and the path is not absolute, include path kicks in.
 * First, -I options, in the order found on the command line.
 * Then M4PATH env variable
 */

struct path_entry {
	char *name;
	struct path_entry *next;
} *first, *last;

static struct path_entry *new_path_entry(const char *);
static void ensure_m4path(void);
static struct input_file *dopath(struct input_file *, const char *);

static struct path_entry *
new_path_entry(const char *dirname)
{
	struct path_entry *n;

	n = malloc(sizeof(struct path_entry));
	if (!n)
		errx(1, "out of memory");
	n->name = strdup(dirname);
	if (!n->name)
		errx(1, "out of memory");
	n->next = 0;
	return n;
}

void
addtoincludepath(const char *dirname)
{
	struct path_entry *n;

	n = new_path_entry(dirname);

	if (last) {
		last->next = n;
		last = n;
	}
	else
		last = first = n;
}

static void
ensure_m4path(void)
{
	static int envpathdone = 0;
	char *envpath;
	char *sweep;
	char *path;

	if (envpathdone)
		return;
	envpathdone = TRUE;
	envpath = getenv("M4PATH");
	if (!envpath)
		return;
	/* for portability: getenv result is read-only */
	envpath = strdup(envpath);
	if (!envpath)
		errx(1, "out of memory");
	for (sweep = envpath;
	    (path = strsep(&sweep, ":")) != NULL;)
	    addtoincludepath(path);
	free(envpath);
}

static
struct input_file *
dopath(struct input_file *i, const char *filename)
{
	char path[MAXPATHLEN];
	struct path_entry *pe;
	FILE *f;

	for (pe = first; pe; pe = pe->next) {
		snprintf(path, sizeof(path), "%s/%s", pe->name, filename);
		if ((f = fopen(path, "r")) != NULL) {
			set_input(i, f, path);
			return i;
		}
	}
	return NULL;
}

struct input_file *
fopen_trypath(struct input_file *i, const char *filename)
{
	FILE *f;

	f = fopen(filename, "r");
	if (f != NULL) {
		set_input(i, f, filename);
		return i;
	}
	if (filename[0] == '/')
		return NULL;

	ensure_m4path();

	return dopath(i, filename);
}

void
doindir(const char *argv[], int argc)
{
	ndptr p;

	p = lookup(argv[2]);
	if (p == NULL)
		errx(1, "undefined macro %s", argv[2]);
	argv[1] = p->defn;
	eval(argv+1, argc-1, p->type);
}

void
dobuiltin(const char *argv[], int argc)
{
	int n;
	argv[1] = NULL;
	n = builtin_type(argv[2]);
	if (n != -1)
		eval(argv+1, argc-1, n);
	else
		errx(1, "unknown builtin %s", argv[2]);
}


/* We need some temporary buffer space, as pb pushes BACK and substitution
 * proceeds forward... */
static char *buffer;
static size_t bufsize = 0;
static size_t current = 0;

static void addchars(const char *, size_t);
static void addchar(int);
static char *twiddle(const char *);
static char *getstring(void);
static void exit_regerror(int, regex_t *);
static void do_subst(const char *, regex_t *, const char *, regmatch_t *);
static void do_regexpindex(const char *, regex_t *, regmatch_t *);
static void do_regexp(const char *, regex_t *, const char *, regmatch_t *);
static void add_sub(size_t, const char *, regex_t *, regmatch_t *);
static void add_replace(const char *, regex_t *, const char *, regmatch_t *);
#define addconstantstring(s) addchars((s), sizeof(s)-1)

static void
addchars(const char *c, size_t n)
{
	if (n == 0)
		return;
	while (current + n > bufsize) {
		if (bufsize == 0)
			bufsize = 1024;
		else
			bufsize *= 2;
		buffer = realloc(buffer, bufsize);
		if (buffer == NULL)
			errx(1, "out of memory");
	}
	memcpy(buffer+current, c, n);
	current += n;
}

static void
addchar(int c)
{
	if (current +1 > bufsize) {
		if (bufsize == 0)
			bufsize = 1024;
		else
			bufsize *= 2;
		buffer = realloc(buffer, bufsize);
		if (buffer == NULL)
			errx(1, "out of memory");
	}
	buffer[current++] = c;
}

static char *
getstring(void)
{
	addchar('\0');
	current = 0;
	return buffer;
}


static void
exit_regerror(int er, regex_t *re)
{
	size_t 	errlen;
	char 	*errbuf;

	errlen = regerror(er, re, NULL, 0);
	errbuf = xalloc(errlen);
	regerror(er, re, errbuf, errlen);
	errx(1, "regular expression error: %s", errbuf);
}

static void
add_sub(size_t n, const char *string, regex_t *re, regmatch_t *pm)
{
	if (n > re->re_nsub)
		warnx("No subexpression %zu", n);
	/* Subexpressions that did not match are
	 * not an error.  */
	else if (pm[n].rm_so != -1 &&
	    pm[n].rm_eo != -1) {
		addchars(string + pm[n].rm_so,
			pm[n].rm_eo - pm[n].rm_so);
	}
}

/* Add replacement string to the output buffer, recognizing special
 * constructs and replacing them with substrings of the original string.
 */
static void
add_replace(const char *string, regex_t *re, const char *replace, regmatch_t *pm)
{
	const char *p;

	for (p = replace; *p != '\0'; p++) {
		if (*p == '\\') {
			if (p[1] == '\\') {
				addchar(p[1]);
				p++;
				continue;
			}
			if (p[1] == '&') {
				add_sub(0, string, re, pm);
				p++;
				continue;
			}
			if (isdigit(p[1])) {
				add_sub(*(++p) - '0', string, re, pm);
				continue;
			}
		}
	    	addchar(*p);
	}
}

static void
do_subst(const char *string, regex_t *re, const char *replace, regmatch_t *pm)
{
	int error;
	int flags = 0;
	const char *last_match = NULL;

	while ((error = regexec(re, string, re->re_nsub+1, pm, flags)) == 0) {
		if (pm[0].rm_eo != 0) {
			if (string[pm[0].rm_eo-1] == '\n')
				flags = 0;
			else
				flags = REG_NOTBOL;
		}

		/* NULL length matches are special... We use the `vi-mode'
		 * rule: don't allow a NULL-match at the last match
		 * position.
		 */
		if (pm[0].rm_so == pm[0].rm_eo &&
		    string + pm[0].rm_so == last_match) {
			if (*string == '\0')
				return;
			addchar(*string);
			if (*string++ == '\n')
				flags = 0;
			else
				flags = REG_NOTBOL;
			continue;
		}
		last_match = string + pm[0].rm_so;
		addchars(string, pm[0].rm_so);
		add_replace(string, re, replace, pm);
		string += pm[0].rm_eo;
	}
	if (error != REG_NOMATCH)
		exit_regerror(error, re);
	pbstr(string);
}

static void
do_regexp(const char *string, regex_t *re, const char *replace, regmatch_t *pm)
{
	int error;

	switch(error = regexec(re, string, re->re_nsub+1, pm, 0)) {
	case 0:
		add_replace(string, re, replace, pm);
		pbstr(getstring());
		break;
	case REG_NOMATCH:
		break;
	default:
		exit_regerror(error, re);
	}
}

static void
do_regexpindex(const char *string, regex_t *re, regmatch_t *pm)
{
	int error;

	switch(error = regexec(re, string, re->re_nsub+1, pm, 0)) {
	case 0:
		pbunsigned(pm[0].rm_so);
		break;
	case REG_NOMATCH:
		pbnum(-1);
		break;
	default:
		exit_regerror(error, re);
	}
}

/* In Gnu m4 mode, parentheses for backmatch don't work like POSIX 1003.2
 * says. So we twiddle with the regexp before passing it to regcomp.
 */
static char *
twiddle(const char *p)
{
	/* This could use strcspn for speed... */
	while (*p != '\0') {
		if (*p == '\\') {
			switch(p[1]) {
			case '(':
			case ')':
			case '|':
				addchar(p[1]);
				break;
			case 'w':
				addconstantstring("[_a-zA-Z0-9]");
				break;
			case 'W':
				addconstantstring("[^_a-zA-Z0-9]");
				break;
			case '<':
				addconstantstring("[[:<:]]");
				break;
			case '>':
				addconstantstring("[[:>:]]");
				break;
			default:
				addchars(p, 2);
				break;
			}
			p+=2;
			continue;
		}
		if (*p == '(' || *p == ')' || *p == '|')
			addchar('\\');

		addchar(*p);
		p++;
	}
	return getstring();
}

/* patsubst(string, regexp, opt replacement) */
/* argv[2]: string
 * argv[3]: regexp
 * argv[4]: opt rep
 */
void
dopatsubst(const char *argv[], int argc)
{
	int error;
	regex_t re;
	regmatch_t *pmatch;

	if (argc <= 3) {
		warnx("Too few arguments to patsubst");
		return;
	}
	error = regcomp(&re, twiddle(argv[3]), REG_NEWLINE | REG_EXTENDED);
	if (error != 0)
		exit_regerror(error, &re);

	pmatch = xalloc(sizeof(regmatch_t) * (re.re_nsub+1));
	do_subst(argv[2], &re,
	    argc != 4 && argv[4] != NULL ? argv[4] : "", pmatch);
	pbstr(getstring());
	free(pmatch);
	regfree(&re);
}

void
doregexp(const char *argv[], int argc)
{
	int error;
	regex_t re;
	regmatch_t *pmatch;

	if (argc <= 3) {
		warnx("Too few arguments to regexp");
		return;
	}
	error = regcomp(&re, twiddle(argv[3]), REG_EXTENDED);
	if (error != 0)
		exit_regerror(error, &re);

	pmatch = xalloc(sizeof(regmatch_t) * (re.re_nsub+1));
	if (argv[4] == NULL || argc == 4)
		do_regexpindex(argv[2], &re, pmatch);
	else
		do_regexp(argv[2], &re, argv[4], pmatch);
	free(pmatch);
	regfree(&re);
}

void
doesyscmd(const char *cmd)
{
	int p[2];
	pid_t pid, cpid;
	int cc;
	int status;

	/* Follow gnu m4 documentation: first flush buffers. */
	fflush(NULL);

	/* Just set up standard output, share stderr and stdin with m4 */
	if (pipe(p) == -1)
		err(1, "bad pipe");
	switch(cpid = fork()) {
	case -1:
		err(1, "bad fork");
		/* NOTREACHED */
	case 0:
		(void) close(p[0]);
		(void) dup2(p[1], 1);
		(void) close(p[1]);
		execl(_PATH_BSHELL, "sh", "-c", cmd, (char *)NULL);
		exit(1);
	default:
		/* Read result in two stages, since m4's buffer is
		 * pushback-only. */
		(void) close(p[1]);
		do {
			char result[BUFSIZE];
			cc = read(p[0], result, sizeof result);
			if (cc > 0)
				addchars(result, cc);
		} while (cc > 0 || (cc == -1 && errno == EINTR));

		(void) close(p[0]);
		while ((pid = wait(&status)) != cpid && pid >= 0)
			continue;
		pbstr(getstring());
	}
}

char
*prefix_dup(const char *s) {
	char *result = xalloc(strlen(s)+4);
	strcpy(result, "m4_");
	strcpy(result+3, s);
	return result;
}

void
do_freeze()
{
	int i;
	ndptr p;
	FILE *f;
	char *buf;
	size_t bufsiz, amtread;

	f = fopen(freeze_filename, "w");
	if (!f)
		err(1, "opening %s: ", freeze_filename);
	fprintf(f, "# Freeze state file generated by Quasar M4\nV1\n");
	for (i = 0; i < HASHSIZE; i++)
		for (p = hashtab[i]; p; p = p->nxtptr) {
			if (p->type == MACRTYPE)
				fprintf(f, "T%zd,%zd\n%s%s\n", strlen(p->name),
					strlen(p->defn), p->name, p->defn);
			else
				fprintf(f, "F%zd,%zd\n%s%s\n", strlen(p->name),
					strlen(p->name), p->name, p->name);
		}
	buf = malloc(1024);
	bufsiz = 1024;
	for (i = 1; i < maxout; i++) {
		if (outfile[i]) {
			rewind(outfile[i]);
			amtread = fread(buf, 1, bufsiz, outfile[i]);
			while (amtread == bufsiz) {
				bufsiz *= 2;
				buf = realloc(buf, bufsiz);
				amtread += fread(buf, 1, bufsiz-amtread,
					outfile[i]);
			}
			fprintf(f, "D%d,%zd\n", i, amtread);
			fwrite(buf, 1, amtread, f);
			fprintf(f, "\n");
			fclose(outfile[i]);
		}
	}
	free(buf);
	fprintf(f, "D0,0\n\n# End of freeze state file\n");
	fclose(f);
}

void
do_restore()
{
	FILE *f;
	ndptr e;
	char lbuf[80];
	size_t l1, l2, r;
	int divnum, ch;
	char *s1, *s2;
	int version = 0;
	f = fopen(restore_filename, "r");
	while (fgets(lbuf, 80, f)) {
		/* Deal with lines that are too long to fit in our buffer; this
			should only happen with comments or invalid files. If
			the file is invalid, we will handle it later. */
		ch = lbuf[strlen(lbuf)-1];
		while (ch != '\n' && ch != -1)
			ch = fgetc(f);

		switch (lbuf[0]) {
		case '#':
		case '\n':
		case '\t':
		case ' ':
		case 0:
			/* Ignore comments and blank lines */
			break;
		case 'V':
			r = sscanf(lbuf+1, "%d", &version);
			if (r < 1)
				errx(1, "freeze state file is corrupt\n");
			break;
		case 'F':
			r = sscanf(lbuf+1, "%zd,%zd", &l1, &l2);
			if (r < 2)
				errx(1, "freeze state file is corrupt\n");
			s1 = malloc(l1+1);
			s2 = malloc(l2+1);
			r = fread(s1, 1, l1, f);
			if (r < l1)
				errx(1, "freeze state file is corrupt\n");
			s1[l1] = 0;
			r = fread(s2, 1, l2, f);
			if (r < l2)
				errx(1, "freeze state file is corrupt\n");
			s2[l2] = 0;
			if (strcmp(s1, s2))
				fprintf(stderr, "warning: should rename \"%s\" to \"%s\"\n",
					s1, s2);
			free(s1);
			free(s2);
			break;
		case 'T':
			r = sscanf(lbuf+1, "%zd,%zd", &l1, &l2);
			if (r < 2)
				errx(1, "freeze state file is corrupt\n");
			s1 = malloc(l1+1);
			s2 = malloc(l2+1);
			r = fread(s1, 1, l1, f);
			if (r < l1)
				errx(1, "freeze state file is corrupt\n");
			s1[l1] = 0;
			r = fread(s2, 1, l2, f);
			if (r < l2)
				errx(1, "freeze state file is corrupt\n");
			s2[l2] = 0;
			/* Define s1 as s2 */
			e = addent(s1);
			e->defn = xstrdup(s2);
			e->type = MACRTYPE;
			free(s1);
			free(s2);
			break;
		case 'D':
			r = sscanf(lbuf+1, "%d,%zd", &divnum, &l1);
			if (r < 2)
				errx(1, "freeze state file is corrupt\n");
			s1 = malloc(l1+1);
			r = fread(s1, 1, l1, f);
			if (r < l1)
				errx(1, "freeze state file is corrupt\n");
			s1[l1] = 0;
			dodiv(divnum);
			fprintf(active, "%s", s1);
			free(s1);
			break;
		default:
			errx(1, "unknown feature %c in freeze state file\n",
				lbuf[0]);
		}
	}
	if (!feof(f))
		errx(1, "freeze state file is corrupt\n");
	fclose(f);
}
